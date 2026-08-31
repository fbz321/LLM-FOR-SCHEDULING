#!/usr/bin/env python3
"""Merge exact manifest results and verify shortlisted fixed sequences."""

import argparse
import json
import os
from fractions import Fraction

import incremental_verify as verifier

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_TAU = Fraction(1748334970307, 1000000000000)


def load_flat_cache(path):
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("version") != 1:
        raise ValueError("unsupported cache version")
    values = {}
    for key, entry in payload.get("entries", {}).items():
        if isinstance(entry, dict):
            values[key] = int(entry["opt"])
        else:
            values[key] = int(entry)
    return values


def verify_candidates(analysis, base_cache, result_cache, m, tau):
    opt_values = dict(base_cache)
    opt_values.update(result_cache)
    records = []
    complete = 0
    for candidate in analysis["candidates"]:
        jobs = tuple(int(job) for job in candidate["jobs"])
        missing = []
        opt_pref = [0]
        for length in range(1, len(jobs) + 1):
            key = verifier.prefix_key(m, jobs[:length])
            if key not in opt_values:
                missing.append({"length": length, "key": key})
            else:
                opt_pref.append(opt_values[key])
        record = {
            "candidate_id": candidate["candidate_id"],
            "multipliers": candidate["multipliers"],
            "missing": missing,
        }
        if not missing:
            complete += 1
            result = verifier.threshold_check(
                jobs, m, tau, opt_pref, include_path=True,
            )
            if not result["passed"]:
                ratios = [
                    (
                        Fraction(
                            max(int(load) for load in step["next_loads"]),
                            opt_pref[step["index"] + 1],
                        ),
                        step["index"] + 1,
                    )
                    for step in result["escape_path"]
                ]
                maximum, prefix = max(ratios)
                result["escape_max_ratio"] = (
                    f"{maximum.numerator}/{maximum.denominator}"
                )
                result["escape_max_ratio_decimal"] = float(maximum)
                result["escape_max_prefix"] = prefix
            record.update(result)
        records.append(record)
    passes = [record for record in records if record.get("passed")]
    return {
        "method": "exact fixed-sequence threshold game",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "tau_decimal": float(tau),
        "candidate_count": len(records),
        "complete_candidates": complete,
        "pass_count": len(passes),
        "passes": passes,
        "candidates": records,
    }


def atomic_json(path, payload):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--analysis", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_analysis.json"))
    parser.add_argument("--base-cache", default=os.path.join(
        HERE, "results", "m5_structured", "prefix_opts_content.json"))
    parser.add_argument("--result-cache", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_opt_results.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_exact_check.json"))
    parser.add_argument("--tau", default=str(DEFAULT_TAU))
    args = parser.parse_args()

    with open(args.analysis, encoding="utf-8") as handle:
        analysis = json.load(handle)
    base = load_flat_cache(args.base_cache)
    results = load_flat_cache(args.result_cache) if os.path.exists(
        args.result_cache) else {}
    payload = verify_candidates(analysis, base, results, 5, Fraction(args.tau))
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "complete_candidates": payload["complete_candidates"],
        "pass_count": payload["pass_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
