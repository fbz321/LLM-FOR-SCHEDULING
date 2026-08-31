#!/usr/bin/env python3
"""Incremental exact verifier for fixed online-scheduling sequences.

Prefix OPT values are content-addressed by the exact integer multiset, not by
prefix length. This makes reuse across reordered or suffix-mutated candidates
safe while retaining the threshold-game semantics used by check_rudin.py.
"""

import hashlib
import json
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m4_search import opt

CACHE_VERSION = 1


def to_int_jobs(sizes):
    """Scale exact rational sizes to their least common integer scale."""
    scale = 1
    for size in sizes:
        scale = math.lcm(scale, size.denominator)
    jobs = tuple(int(size * scale) for size in sizes)
    if any(job <= 0 for job in jobs):
        raise ValueError("job sizes must be positive")
    return jobs, scale


def canonical_prefix(prefix):
    return tuple(sorted((int(job) for job in prefix), reverse=True))


def prefix_key(m, prefix):
    canonical = f"{int(m)}:" + ",".join(
        str(job) for job in canonical_prefix(prefix)
    )
    return hashlib.sha256(canonical.encode("ascii")).hexdigest()


def empty_cache():
    return {"version": CACHE_VERSION, "entries": {}}


def load_cache(path):
    if path is None or not os.path.exists(path):
        return empty_cache()
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("version") != CACHE_VERSION:
        raise ValueError("unsupported prefix cache version")
    entries = payload.get("entries")
    if not isinstance(entries, dict):
        raise ValueError("prefix cache entries must be an object")
    return payload


def save_cache(path, cache):
    if path is None:
        return
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(cache, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def _validated_entry(entry, m, prefix):
    if not isinstance(entry, dict):
        raise ValueError("prefix cache entry must be an object")
    expected_jobs = canonical_prefix(prefix)
    cached_m = entry.get("m")
    cached_jobs = entry.get("jobs")
    cached_opt = entry.get("opt")
    if cached_m != m or cached_jobs != [str(job) for job in expected_jobs]:
        raise ValueError("prefix cache entry does not match its content key")
    try:
        value = int(cached_opt)
    except (TypeError, ValueError) as error:
        raise ValueError("prefix cache OPT must be an integer string") from error
    if value <= 0:
        raise ValueError("prefix cache OPT must be positive")
    return value


def put_opt(cache, m, prefix, value):
    value = int(value)
    if value <= 0:
        raise ValueError("prefix OPT must be positive")
    jobs = canonical_prefix(prefix)
    key = prefix_key(m, jobs)
    cache["entries"][key] = {
        "m": int(m),
        "jobs": [str(job) for job in jobs],
        "opt": str(value),
    }
    return key


def import_index_cache(cache, jobs, m, indexed):
    """Import a legacy {prefix_length: OPT} cache bound to one exact sequence."""
    expected = {str(length) for length in range(1, len(jobs) + 1)}
    extra = set(indexed) - expected
    if extra:
        raise ValueError(f"legacy cache has unexpected prefix keys: {sorted(extra)}")
    for length_text, value in indexed.items():
        length = int(length_text)
        put_opt(cache, m, jobs[:length], int(value))
    return cache


def prepare_prefix_opts(jobs, m, cache=None, cache_path=None, solver=opt,
                        allow_compute=True):
    """Return exact OPT by prefix length and update a validated content cache."""
    if cache is None:
        cache = load_cache(cache_path)
    entries = cache["entries"]
    values = [0]
    hits = 0
    misses = 0
    for length in range(1, len(jobs) + 1):
        prefix = jobs[:length]
        key = prefix_key(m, prefix)
        entry = entries.get(key)
        if entry is not None:
            value = _validated_entry(entry, m, prefix)
            hits += 1
        else:
            if not allow_compute:
                raise KeyError(f"missing exact OPT for prefix {length}: {key}")
            value = int(solver(canonical_prefix(prefix), m))
            put_opt(cache, m, prefix, value)
            save_cache(cache_path, cache)
            misses += 1
        values.append(value)
    return values, cache, {"hits": hits, "misses": misses}


def threshold_check(jobs, m, tau, opt_pref, include_path=False):
    """Check whether every scheduler path reaches ratio at least ``tau``."""
    tau = Fraction(tau)
    if len(opt_pref) != len(jobs) + 1:
        raise ValueError("opt_pref length does not match job sequence")
    numerator, denominator = tau.numerator, tau.denominator
    memo = {}
    violating = set()
    choices = {} if include_path else None

    def winning(index, loads):
        key = (index, loads)
        if key in memo:
            return memo[key]
        if (opt_pref[index] > 0 and
                max(loads) * denominator >= numerator * opt_pref[index]):
            memo[key] = True
            violating.add(key)
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
                if choices is not None:
                    choices[key] = next_loads
                return False
        memo[key] = True
        return True

    passed = winning(0, (0,) * m)
    path = []
    if include_path and not passed:
        index = 0
        loads = (0,) * m
        while (index, loads) in choices:
            next_loads = choices[(index, loads)]
            path.append({
                "index": index,
                "job": str(jobs[index]),
                "loads": [str(load) for load in loads],
                "next_loads": [str(load) for load in next_loads],
            })
            index += 1
            loads = next_loads
    return {
        "passed": passed,
        "states": len(memo),
        "violating_states": len(violating),
        "escape_path": path,
    }


def verify(jobs, m, tau, cache=None, cache_path=None, solver=opt,
           allow_compute=True, include_path=False):
    opt_pref, cache, stats = prepare_prefix_opts(
        jobs, m, cache=cache, cache_path=cache_path, solver=solver,
        allow_compute=allow_compute,
    )
    result = threshold_check(
        jobs, m, tau, opt_pref, include_path=include_path,
    )
    result["cache"] = stats
    return result, cache
