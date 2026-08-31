#!/usr/bin/env python3
"""Certify scheduler escape paths with a mix of exact OPT and safe bounds.

For each prefix on the deterministic least-loaded-machine path, use exact OPT
when available. Otherwise use the basic lower bound. Since lower_bound <= OPT,
`makespan / lower_bound` is an upper bound on the true ratio. A candidate is
certifiably rejected when every such upper bound is below the target.
"""

import argparse
import json
import math
import os
from fractions import Fraction

import incremental_verify as verifier
from m5_verify_shortlist import atomic_json, load_flat_cache

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_TAU = Fraction(1748334970307, 1000000000000)


def basic_lower_bound(prefix, m):
    return max(max(prefix), math.ceil(sum(prefix) / m))


def certify_path(jobs, m, tau, exact_values):
    loads = [0] * m
    maximum = Fraction(0)
    maximum_prefix = 0
    exact_prefixes = 0
    bounded_prefixes = 0
    unresolved = []
    for length, job in enumerate(jobs, 1):
        machine = min(range(m), key=lambda index: (loads[index], index))
        loads[machine] += job
        prefix = jobs[:length]
        lower = basic_lower_bound(prefix, m)
        bound_ratio = Fraction(max(loads), lower)
        key = verifier.prefix_key(m, prefix)
        if key in exact_values:
            denominator = exact_values[key]
            exact_prefixes += 1
        elif bound_ratio < tau:
            denominator = lower
            bounded_prefixes += 1
        else:
            unresolved.append({
                "length": length,
                "key": key,
                "bound_ratio": (
                    f"{bound_ratio.numerator}/{bound_ratio.denominator}"
                ),
            })
            continue
        ratio_upper = Fraction(max(loads), denominator)
        if ratio_upper > maximum:
            maximum = ratio_upper
            maximum_prefix = length
    return {
        "escaped": not unresolved and maximum < tau,
        "maximum_ratio_upper": f"{maximum.numerator}/{maximum.denominator}",
        "maximum_ratio_upper_decimal": float(maximum),
        "maximum_prefix": maximum_prefix,
        "exact_prefixes": exact_prefixes,
        "bounded_prefixes": bounded_prefixes,
        "unresolved": unresolved,
    }


def bounded_threshold_game(jobs, m, tau, exact_values):
    """Search all scheduler placements against safe prefix OPT lower bounds.

    Exact OPT values are used when available and the basic lower bound is used
    otherwise.  Failure of this easier adversary game is a rigorous scheduler
    escape for the true game because every supplied denominator is at most OPT.
    A pass is deliberately reported as unresolved rather than as a lower bound.
    """
    denominators = [0]
    exact_prefixes = 0
    bounded_prefixes = 0
    for length in range(1, len(jobs) + 1):
        prefix = jobs[:length]
        key = verifier.prefix_key(m, prefix)
        if key in exact_values:
            denominators.append(exact_values[key])
            exact_prefixes += 1
        else:
            denominators.append(basic_lower_bound(prefix, m))
            bounded_prefixes += 1

    result = verifier.threshold_check(
        jobs, m, tau, denominators, include_path=True,
    )
    record = {
        "escaped": not result["passed"],
        "states": result["states"],
        "violating_states": result["violating_states"],
        "exact_prefixes": exact_prefixes,
        "bounded_prefixes": bounded_prefixes,
    }
    if result["passed"]:
        return record

    ratios = [
        (
            Fraction(
                max(int(load) for load in step["next_loads"]),
                denominators[step["index"] + 1],
            ),
            step["index"] + 1,
        )
        for step in result["escape_path"]
    ]
    maximum, prefix = max(ratios)
    record.update({
        "maximum_ratio_upper": f"{maximum.numerator}/{maximum.denominator}",
        "maximum_ratio_upper_decimal": float(maximum),
        "maximum_prefix": prefix,
    })
    return record


def certify_candidates(analysis, m, tau, exact_values):
    records = []
    path_escapes = 0
    game_escapes = 0
    for candidate in analysis["candidates"]:
        jobs = tuple(int(job) for job in candidate["jobs"])
        path_result = certify_path(jobs, m, tau, exact_values)
        record = {
            "candidate_id": candidate["candidate_id"],
            "multipliers": candidate.get("multipliers", []),
            "path": path_result,
        }
        if path_result["escaped"]:
            path_escapes += 1
            record.update({
                "escaped": True,
                "certificate": "mixed-bound least-loaded scheduler escape",
            })
        else:
            game_result = bounded_threshold_game(
                jobs, m, tau, exact_values,
            )
            record["bounded_game"] = game_result
            record["escaped"] = game_result["escaped"]
            if game_result["escaped"]:
                game_escapes += 1
                record["certificate"] = (
                    "mixed-bound threshold-game scheduler escape"
                )
            else:
                record["certificate"] = "unresolved by safe lower bounds"
        records.append(record)
    return {
        "version": 2,
        "method": "mixed exact-OPT/basic-bound scheduler escape certificates",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "candidate_count": len(records),
        "path_escapes": path_escapes,
        "bounded_game_escapes": game_escapes,
        "escaped": path_escapes + game_escapes,
        "unresolved_count": len(records) - path_escapes - game_escapes,
        "candidates": records,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--analysis", required=True)
    parser.add_argument("--exact-cache", action="append", default=[])
    parser.add_argument("--output", required=True)
    parser.add_argument("--m", type=int, default=5)
    parser.add_argument("--tau", default=str(DEFAULT_TAU))
    args = parser.parse_args()

    with open(args.analysis, encoding="utf-8") as handle:
        analysis = json.load(handle)
    exact_values = {}
    for path in args.exact_cache:
        if os.path.exists(path):
            exact_values.update(load_flat_cache(path))
    payload = certify_candidates(
        analysis, args.m, Fraction(args.tau), exact_values,
    )
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "escaped": payload["escaped"],
        "unresolved_count": payload["unresolved_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
