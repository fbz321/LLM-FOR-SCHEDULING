#!/usr/bin/env python3
"""Compact exact certification for every candidate in a structured grid.

A single scheduler path whose ratio stays below the target certifies that the
fixed sequence fails.  The deterministic least-loaded-machine path is checked
first using exact prefix OPT values.  Only candidates not settled by that path
are sent to the full threshold game.  Escape paths are summarized rather than
stored verbatim so exhaustive-grid artifacts remain small.
"""

import argparse
import json
import os
from fractions import Fraction

import incremental_verify as verifier
from m5_verify_shortlist import atomic_json, load_flat_cache

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_TAU = Fraction(1748334970307, 1000000000000)


def exact_opts(jobs, m, values):
    opts = [0]
    missing = []
    for length in range(1, len(jobs) + 1):
        key = verifier.prefix_key(m, jobs[:length])
        if key in values:
            opts.append(values[key])
        else:
            missing.append({"length": length, "key": key})
    return opts, missing


def least_loaded_path(jobs, m, opt_pref):
    loads = [0] * m
    maximum = Fraction(0)
    maximum_prefix = 0
    for length, job in enumerate(jobs, 1):
        machine = min(range(m), key=lambda index: (loads[index], index))
        loads[machine] += job
        ratio = Fraction(max(loads), opt_pref[length])
        if ratio > maximum:
            maximum = ratio
            maximum_prefix = length
    return maximum, maximum_prefix


def path_maximum(path, opt_pref):
    ratios = [
        (
            Fraction(
                max(int(load) for load in step["next_loads"]),
                opt_pref[step["index"] + 1],
            ),
            step["index"] + 1,
        )
        for step in path
    ]
    return max(ratios)


def certify_candidates(analysis, base_cache, result_cache, m, tau):
    values = dict(base_cache)
    values.update(result_cache)
    records = []
    complete = 0
    direct_escapes = 0
    game_escapes = 0
    passes = 0

    for candidate in analysis["candidates"]:
        jobs = tuple(int(job) for job in candidate["jobs"])
        opt_pref, missing = exact_opts(jobs, m, values)
        record = {
            "candidate_id": candidate["candidate_id"],
            "multipliers": candidate.get("multipliers", []),
            "missing": missing,
        }
        if missing:
            records.append(record)
            continue

        complete += 1
        maximum, prefix = least_loaded_path(jobs, m, opt_pref)
        record.update({
            "least_loaded_max_ratio": (
                f"{maximum.numerator}/{maximum.denominator}"
            ),
            "least_loaded_max_ratio_decimal": float(maximum),
            "least_loaded_max_prefix": prefix,
        })
        if maximum < tau:
            direct_escapes += 1
            record["passed"] = False
            record["certificate"] = "exact least-loaded scheduler escape"
            records.append(record)
            continue

        result = verifier.threshold_check(
            jobs, m, tau, opt_pref, include_path=True,
        )
        record.update({
            "passed": result["passed"],
            "states": result["states"],
            "violating_states": result["violating_states"],
        })
        if result["passed"]:
            passes += 1
            record["certificate"] = "exact threshold-game PASS"
        else:
            game_escapes += 1
            escape_maximum, escape_prefix = path_maximum(
                result["escape_path"], opt_pref,
            )
            record.update({
                "certificate": "exact threshold-game scheduler escape",
                "escape_max_ratio": (
                    f"{escape_maximum.numerator}/{escape_maximum.denominator}"
                ),
                "escape_max_ratio_decimal": float(escape_maximum),
                "escape_max_prefix": escape_prefix,
            })
        records.append(record)

    return {
        "version": 1,
        "method": "compact exact fixed-sequence grid certification",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "tau_decimal": float(tau),
        "candidate_count": len(records),
        "complete_candidates": complete,
        "direct_scheduler_escapes": direct_escapes,
        "threshold_game_escapes": game_escapes,
        "pass_count": passes,
        "candidates": records,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--analysis", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_full_analysis.json"))
    parser.add_argument("--base-cache", default=os.path.join(
        HERE, "results", "m5_structured", "prefix_opts_content.json"))
    parser.add_argument("--result-cache", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_full_opt_results.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_full_exact_check.json"))
    parser.add_argument("--tau", default=str(DEFAULT_TAU))
    args = parser.parse_args()

    with open(args.analysis, encoding="utf-8") as handle:
        analysis = json.load(handle)
    base = load_flat_cache(args.base_cache)
    results = load_flat_cache(args.result_cache) if os.path.exists(
        args.result_cache) else {}
    payload = certify_candidates(
        analysis, base, results, 5, Fraction(args.tau),
    )
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "complete_candidates": payload["complete_candidates"],
        "direct_scheduler_escapes": payload["direct_scheduler_escapes"],
        "threshold_game_escapes": payload["threshold_game_escapes"],
        "pass_count": payload["pass_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
