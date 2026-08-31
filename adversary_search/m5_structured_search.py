#!/usr/bin/env python3
"""Exhaustive structured search around the Rudin m=5 Table A2 sequence.

The first neighborhood preserves every job size and every five-job block, but
moves the singleton within each 4+1 mixed block.  There are 5**6 candidates.
Prefix OPT values are keyed by the sorted prefix multiset, so all candidates
share the same small set of exact computations.
"""

import argparse
import itertools
import json
import math
import multiprocessing as mp
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import template_schema
import incremental_verify as verifier
from m4_search import opt

_BASE_JOBS = ()
_BLOCKS = ()
_OPT_BY_KEY = {}
_TAU = Fraction(0)
_M = 5
DEFAULT_TAU = Fraction(1748334970307, 1000000000000)


def atomic_json(path, payload):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def load_seed(path):
    with open(path, encoding="utf-8") as handle:
        template = json.load(handle)
    sizes, metadata = template_schema.materialize(template)
    scale = 1
    for size in sizes:
        scale = math.lcm(scale, size.denominator)
    jobs = tuple(int(size * scale) for size in sizes)
    return template, jobs, metadata["m"], scale


def mixed_blocks(template):
    """Return (start, small, singleton) for adjacent 4+1 layer pairs."""
    result = []
    offset = 0
    layers = template["layers"]
    i = 0
    while i < len(layers):
        emits = layers[i]["emit"]
        repeat = int(emits[0].get("repeat", 1)) if len(emits) == 1 else -1
        if repeat == 4 and i + 1 < len(layers):
            next_emits = layers[i + 1]["emit"]
            next_repeat = (int(next_emits[0].get("repeat", 1))
                           if len(next_emits) == 1 else -1)
            if next_repeat == 1:
                result.append((offset, int(emits[0]["size"]),
                               int(next_emits[0]["size"])))
                offset += 5
                i += 2
                continue
        offset += sum(int(item.get("repeat", 1)) for item in emits)
        i += 1
    return tuple(result)


def prefix_key(m, prefix):
    return verifier.prefix_key(m, prefix)


def candidate_jobs(base_jobs, blocks, positions):
    jobs = list(base_jobs)
    for (start, small, singleton), position in zip(blocks, positions):
        jobs[start:start + 5] = ([small] * position + [singleton]
                                + [small] * (4 - position))
    return tuple(jobs)


def required_prefixes(base_jobs, blocks, m):
    required = {}
    for positions in itertools.product(range(5), repeat=len(blocks)):
        jobs = candidate_jobs(base_jobs, blocks, positions)
        for start, _, _ in blocks:
            for length in range(start + 1, start + 6):
                key = prefix_key(m, jobs[:length])
                required.setdefault(key, tuple(sorted(jobs[:length], reverse=True)))
    return required


def import_index_cache(base_jobs, m, path):
    with open(path, encoding="utf-8") as handle:
        indexed = json.load(handle)
    imported = {}
    for index, value in indexed.items():
        length = int(index)
        imported[prefix_key(m, base_jobs[:length])] = str(value)
    return imported


def load_content_cache(path):
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("version") != 1:
        raise ValueError("unsupported content cache version")
    return dict(payload.get("entries", {}))


def save_content_cache(path, entries):
    atomic_json(path, {"version": 1, "entries": entries})


def compute_opt_task(item):
    key, jobs = item
    return key, str(opt(tuple(jobs), _M))


def initialize_opt_worker(m):
    global _M
    _M = m


def prepare_cache(base_jobs, blocks, m, index_cache, content_cache, workers):
    entries = load_content_cache(content_cache)
    entries.update(import_index_cache(base_jobs, m, index_cache))
    save_content_cache(content_cache, entries)

    required = required_prefixes(base_jobs, blocks, m)
    missing = [(key, jobs) for key, jobs in required.items() if key not in entries]
    print(f"required={len(required)} cached={len(required)-len(missing)} "
          f"missing={len(missing)}", flush=True)
    if not missing:
        return entries

    method = "fork" if "fork" in mp.get_all_start_methods() else "spawn"
    context = mp.get_context(method)
    started = time.time()
    with context.Pool(min(workers, len(missing)), initializer=initialize_opt_worker,
                      initargs=(m,)) as pool:
        for completed, (key, value) in enumerate(
                pool.imap_unordered(compute_opt_task, missing), 1):
            entries[key] = value
            save_content_cache(content_cache, entries)
            print(f"OPT {completed}/{len(missing)} done elapsed="
                  f"{time.time()-started:.1f}s", flush=True)
    return entries


def exact_threshold_check(jobs, m, tau, opt_by_key, include_path=False):
    opt_pref = [0]
    for length in range(1, len(jobs) + 1):
        key = prefix_key(m, jobs[:length])
        if key not in opt_by_key:
            raise KeyError(f"missing OPT for prefix {length}: {key}")
        opt_pref.append(int(opt_by_key[key]))

    numerator, denominator = tau.numerator, tau.denominator
    memo = {}
    choice = {} if include_path else None

    def winning(index, loads):
        key = (index, loads)
        if key in memo:
            return memo[key]
        if (opt_pref[index] > 0 and
                max(loads) * denominator >= numerator * opt_pref[index]):
            memo[key] = True
            return True
        if index == len(jobs):
            memo[key] = False
            return False

        job = jobs[index]
        seen = set()
        for machine, load in enumerate(loads):
            if load in seen:
                continue
            seen.add(load)
            updated = list(loads)
            updated[machine] += job
            next_loads = tuple(sorted(updated))
            if not winning(index + 1, next_loads):
                memo[key] = False
                if choice is not None:
                    choice[key] = next_loads
                return False
        memo[key] = True
        return True

    result = winning(0, (0,) * m)
    path = []
    if include_path and not result:
        index, loads = 0, (0,) * m
        while (index, loads) in choice:
            next_loads = choice[(index, loads)]
            path.append({"index": index, "job": str(jobs[index]),
                         "loads": [str(x) for x in loads],
                         "next_loads": [str(x) for x in next_loads]})
            index += 1
            loads = next_loads
    return result, len(memo), path


def initialize_screen_worker(base_jobs, blocks, opt_by_key, tau, m):
    global _BASE_JOBS, _BLOCKS, _OPT_BY_KEY, _TAU, _M
    _BASE_JOBS = base_jobs
    _BLOCKS = blocks
    _OPT_BY_KEY = opt_by_key
    _TAU = tau
    _M = m


def screen_task(positions):
    jobs = candidate_jobs(_BASE_JOBS, _BLOCKS, positions)
    passed, states, _ = exact_threshold_check(jobs, _M, _TAU, _OPT_BY_KEY)
    return positions, passed, states


def screen(base_jobs, blocks, m, tau, entries, workers, output):
    configs = list(itertools.product(range(5), repeat=len(blocks)))
    method = "fork" if "fork" in mp.get_all_start_methods() else "spawn"
    context = mp.get_context(method)
    started = time.time()
    passes = []
    min_states = None
    max_states = 0
    baseline = None

    with context.Pool(min(workers, len(configs)),
                      initializer=initialize_screen_worker,
                      initargs=(base_jobs, blocks, entries, tau, m)) as pool:
        for completed, (positions, passed, states) in enumerate(
                pool.imap_unordered(screen_task, configs, chunksize=8), 1):
            if passed:
                passes.append(list(positions))
            if positions == (4,) * len(blocks):
                baseline = {"passed": passed, "states": states}
            min_states = states if min_states is None else min(min_states, states)
            max_states = max(max_states, states)
            if completed % 1000 == 0:
                print(f"screen {completed}/{len(configs)} passes={len(passes)} "
                      f"elapsed={time.time()-started:.1f}s", flush=True)

    details = []
    for positions in passes:
        jobs = candidate_jobs(base_jobs, blocks, positions)
        passed, states, path = exact_threshold_check(
            jobs, m, tau, entries, include_path=True)
        details.append({"positions": positions, "passed": passed,
                        "states": states, "escape_path": path})

    payload = {
        "method": "singleton-position exhaustive search",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "tau_decimal": float(tau),
        "tested": len(configs),
        "mixed_blocks": [list(block) for block in blocks],
        "baseline_positions": [4] * len(blocks),
        "baseline": baseline,
        "pass_count": len(passes),
        "passes": details,
        "state_range": [min_states, max_states],
        "seconds": time.time() - started,
    }
    atomic_json(output, payload)
    print(json.dumps(payload, indent=2), flush=True)
    return payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", default=os.path.join(HERE, "seeds", "rudin2001_m5.json"))
    parser.add_argument("--index-cache", default=os.path.join(
        HERE, "results", "rudin2001", "cache", "m5_prefix_opts.json"))
    parser.add_argument("--output-dir", default=os.path.join(
        HERE, "results", "m5_structured"))
    parser.add_argument("--tau", default=str(DEFAULT_TAU))
    parser.add_argument("--workers", type=int, default=min(24, os.cpu_count() or 1))
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()

    template, jobs, m, scale = load_seed(args.seed)
    blocks = mixed_blocks(template)
    if m != 5 or len(jobs) != 71 or len(blocks) != 6:
        raise ValueError(f"unexpected baseline m={m} jobs={len(jobs)} blocks={len(blocks)}")
    for start, small, singleton in blocks:
        if jobs[start:start + 5] != (small,) * 4 + (singleton,):
            raise ValueError(f"mixed block mismatch at prefix {start}")

    os.makedirs(args.output_dir, exist_ok=True)
    content_cache = os.path.join(args.output_dir, "prefix_opts_content.json")
    entries = prepare_cache(jobs, blocks, m, args.index_cache,
                            content_cache, args.workers)
    print(f"seed jobs={len(jobs)} scale={scale} blocks={blocks}", flush=True)
    if args.prepare_only:
        return

    output = os.path.join(args.output_dir, "singleton_permutations.json")
    screen(jobs, blocks, m, Fraction(args.tau), entries, args.workers, output)


if __name__ == "__main__":
    main()
