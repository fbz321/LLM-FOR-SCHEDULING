#!/usr/bin/env python3
"""Analyze shortlist candidates using only baseline OPT-safe prefix bounds.

For each candidate, prefixes before its first mutation reuse the exact Rudin
OPT cache. Mutated prefixes use a rigorous lower bound on OPT, yielding an
upper bound on the ratio attained by a selected scheduler path. This is a
ranking/necessary-condition stage, never a lower-bound certificate.
"""

import argparse
import json
import math
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))


def load_baseline(path):
    with open(path, encoding="utf-8") as handle:
        template = json.load(handle)
    jobs = []
    for layer in template["layers"]:
        for emitted in layer["emit"]:
            jobs.extend([int(emitted["size"])] * int(emitted.get("repeat", 1)))
    for emitted in template.get("final", []):
        jobs.extend([int(emitted["size"])] * int(emitted.get("repeat", 1)))
    return tuple(jobs), int(template["m"])


def load_legacy_opts(path):
    with open(path, encoding="utf-8") as handle:
        return {int(length): int(value) for length, value in json.load(handle).items()}


def candidate_jobs(record):
    return tuple(int(job) for job in record["jobs"])


def lpt_loads(jobs, m):
    loads = [0] * m
    for job in jobs:
        machine = min(range(m), key=loads.__getitem__)
        loads[machine] += job
    return tuple(sorted(loads))


def opt_lower_bound(prefix, m):
    return max(max(prefix), math.ceil(sum(prefix) / m))


def evaluate_candidate(jobs, baseline_jobs, baseline_opts, m):
    first_mutation = next(
        (index for index, pair in enumerate(zip(jobs, baseline_jobs))
         if pair[0] != pair[1]),
        len(jobs),
    )
    loads = [0] * m
    best_upper = Fraction(0)
    best_prefix = 0
    for index, job in enumerate(jobs, 1):
        machine = min(range(m), key=loads.__getitem__)
        loads[machine] += job
        if index <= first_mutation:
            denominator = baseline_opts[index]
        else:
            denominator = opt_lower_bound(jobs[:index], m)
        ratio_upper = Fraction(max(loads), denominator)
        if ratio_upper > best_upper:
            best_upper = ratio_upper
            best_prefix = index
    return {
        "first_mutation": first_mutation,
        "list_path_ratio_upper": str(best_upper),
        "list_path_ratio_upper_decimal": float(best_upper),
        "list_path_best_prefix": best_prefix,
        "final_lpt_loads": [str(load) for load in sorted(loads)],
    }


def analyze(shortlist, baseline_jobs, baseline_opts, m, retain):
    records = []
    for record in shortlist["candidates"]:
        jobs = candidate_jobs(record)
        evaluation = evaluate_candidate(
            jobs, baseline_jobs, baseline_opts, m,
        )
        records.append({**record, **evaluation})
    records.sort(
        key=lambda record: (
            Fraction(record["list_path_ratio_upper"]),
            record["candidate_id"],
        ),
        reverse=True,
    )
    return {
        "method": "baseline-safe representative scheduler path analysis",
        "certifying": False,
        "input_candidates": len(records),
        "retained": min(retain, len(records)),
        "candidates": records[:retain],
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
    parser.add_argument("--seed", default=os.path.join(
        HERE, "seeds", "rudin2001_m5.json"))
    parser.add_argument("--cache", default=os.path.join(
        HERE, "results", "rudin2001", "cache", "m5_prefix_opts.json"))
    parser.add_argument("--shortlist", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_shortlist.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_analysis.json"))
    parser.add_argument("--retain", type=int, default=50)
    args = parser.parse_args()

    baseline_jobs, m = load_baseline(args.seed)
    baseline_opts = load_legacy_opts(args.cache)
    with open(args.shortlist, encoding="utf-8") as handle:
        shortlist = json.load(handle)
    payload = analyze(shortlist, baseline_jobs, baseline_opts, m, args.retain)
    atomic_json(args.output, payload)
    print(json.dumps({
        "input_candidates": payload["input_candidates"],
        "retained": payload["retained"],
        "best": payload["candidates"][0] if payload["candidates"] else None,
    }, indent=2))


if __name__ == "__main__":
    main()
