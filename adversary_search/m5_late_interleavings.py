#!/usr/bin/env python3
"""Exhaustively interleave Rudin's last Type-2 and Type-3 interfaces.

The first 60 jobs remain fixed.  The final eleven-job multiset contains four
last-Type-2 A jobs, its singleton, four Type-3 A jobs, its singleton, and the
final job.  Every one of 11!/(4!4!) = 69,300 distinct orders is checked at the
exact rational threshold using content-addressed prefix OPT values.
"""

import argparse
import itertools
import json
import multiprocessing as mp
import os
import time
from fractions import Fraction

import incremental_verify as verifier
from m5_late_interface import load_jobs
from m5_structured_search import load_content_cache

HERE = os.path.dirname(os.path.abspath(__file__))
LATE_START = 60
M = 5
TARGET = Fraction(1748334970307, 1000000000000)

_BASE_JOBS = ()
_CONFIG_VALUES = ()
_OPT_VALUES = {}
_TAU = TARGET


def configurations():
    """Yield all label orders of XXXX t AAAA s f without duplicates."""
    positions = tuple(range(11))
    for type2_positions in itertools.combinations(positions, 4):
        type2_set = set(type2_positions)
        remaining = tuple(index for index in positions if index not in type2_set)
        for type3_positions in itertools.combinations(remaining, 4):
            type3_set = set(type3_positions)
            singleton_positions = tuple(
                index for index in remaining if index not in type3_set
            )
            for singleton_order in itertools.permutations(("t", "s", "f")):
                labels = [None] * 11
                for index in type2_positions:
                    labels[index] = "X"
                for index in type3_positions:
                    labels[index] = "A"
                for index, label in zip(singleton_positions, singleton_order):
                    labels[index] = label
                yield "".join(labels)


def label_values(base_jobs):
    tail = base_jobs[LATE_START:]
    values = {
        "X": base_jobs[60],
        "t": base_jobs[64],
        "A": base_jobs[65],
        "s": base_jobs[69],
        "f": base_jobs[70],
    }
    expected = sorted([values["X"]] * 4 + [values["t"]] +
                      [values["A"]] * 4 + [values["s"], values["f"]])
    if len(tail) != 11 or sorted(tail) != expected:
        raise ValueError("unexpected late-interface multiset")
    return values


def candidate_jobs(base_jobs, config, values=None):
    values = label_values(base_jobs) if values is None else values
    return base_jobs[:LATE_START] + tuple(values[label] for label in config)


def required_prefixes(base_jobs):
    values = label_values(base_jobs)
    required = {}
    for config in configurations():
        jobs = candidate_jobs(base_jobs, config, values)
        for length in range(LATE_START + 1, len(jobs) + 1):
            prefix = jobs[:length]
            key = verifier.prefix_key(M, prefix)
            required.setdefault(key, {
                "key": key,
                "m": M,
                "length": length,
                "jobs": [
                    str(job) for job in verifier.canonical_prefix(prefix)
                ],
                "used_by": [],
            })
    return required


def build_manifest(base_jobs, cached):
    required = required_prefixes(base_jobs)
    missing = [item for key, item in required.items() if key not in cached]
    missing.sort(key=lambda item: (item["length"], item["key"]))
    return {
        "version": 1,
        "method": "late Type-2/Type-3 interleaving exact OPT manifest",
        "candidate_count": 69300,
        "cached_prefixes": len(cached),
        "required_late_prefixes": len(required),
        "missing_prefixes": len(missing),
        "jobs": missing,
    }


def initialize_worker(base_jobs, values, opt_values, tau):
    global _BASE_JOBS, _CONFIG_VALUES, _OPT_VALUES, _TAU
    _BASE_JOBS = base_jobs
    _CONFIG_VALUES = values
    _OPT_VALUES = opt_values
    _TAU = tau


def screen_task(config):
    jobs = candidate_jobs(_BASE_JOBS, config, _CONFIG_VALUES)
    opts = [0]
    for length in range(1, len(jobs) + 1):
        key = verifier.prefix_key(M, jobs[:length])
        if key not in _OPT_VALUES:
            raise KeyError(f"missing OPT for prefix {length}: {key}")
        opts.append(_OPT_VALUES[key])
    result = verifier.threshold_check(jobs, M, _TAU, opts)
    return config, result["passed"], result["states"]


def screen(base_jobs, opt_values, tau=TARGET, workers=None):
    configs = configurations()
    worker_count = min(workers or (os.cpu_count() or 1), 24)
    method = "fork" if "fork" in mp.get_all_start_methods() else "spawn"
    context = mp.get_context(method)
    values = label_values(base_jobs)
    tested = 0
    passes = []
    minimum_states = None
    maximum_states = 0
    started = time.time()
    with context.Pool(
        worker_count,
        initializer=initialize_worker,
        initargs=(base_jobs, values, opt_values, tau),
    ) as pool:
        for config, passed, states in pool.imap_unordered(
            screen_task, configs, chunksize=32,
        ):
            tested += 1
            if passed:
                passes.append(config)
            minimum_states = (
                states if minimum_states is None else min(minimum_states, states)
            )
            maximum_states = max(maximum_states, states)
    return {
        "version": 1,
        "method": "all late Type-2/Type-3 multiset interleavings",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "tested": tested,
        "pass_count": len(passes),
        "passes": sorted(passes),
        "state_range": [minimum_states, maximum_states],
        "seconds": time.time() - started,
    }


def atomic_json(path, payload):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def load_opt_values(*paths):
    values = {}
    for path in paths:
        if not path or not os.path.exists(path):
            continue
        entries = load_content_cache(path)
        for key, entry in entries.items():
            values[key] = int(entry["opt"] if isinstance(entry, dict) else entry)
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", default=os.path.join(
        HERE, "seeds", "rudin2001_m5.json"))
    parser.add_argument("--base-cache", default=os.path.join(
        HERE, "results", "m5_structured", "prefix_opts_content.json"))
    parser.add_argument("--opt-results", default=os.path.join(
        HERE, "results", "m5_structured", "late_interleavings_opt_results.json"))
    parser.add_argument("--manifest", default=os.path.join(
        HERE, "results", "m5_structured", "late_interleavings_opt_manifest.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interleavings_exact_check.json"))
    parser.add_argument("--workers", type=int, default=min(24, os.cpu_count() or 1))
    parser.add_argument("--prepare-manifest", action="store_true")
    args = parser.parse_args()

    base_jobs, m = load_jobs(args.seed)
    if m != M or len(base_jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(base_jobs)}")
    cached = load_opt_values(args.base_cache, args.opt_results)
    if args.prepare_manifest:
        payload = build_manifest(base_jobs, cached)
        atomic_json(args.manifest, payload)
        print(json.dumps({
            "candidate_count": payload["candidate_count"],
            "required_late_prefixes": payload["required_late_prefixes"],
            "missing_prefixes": payload["missing_prefixes"],
        }, indent=2))
        return
    payload = screen(base_jobs, cached, workers=args.workers)
    atomic_json(args.output, payload)
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
