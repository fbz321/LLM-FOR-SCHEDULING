#!/usr/bin/env python3
"""Generate inexpensive late-interface mutations of Rudin's m=5 sequence.

This module does not certify candidates. It enumerates a deterministic,
low-dimensional rational neighborhood and applies only necessary upper-bound
screens that need no new exact OPT computations. Survivors are exported for a
later exact prefix-OPT run.
"""

import argparse
import hashlib
import itertools
import json
import math
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
BASELINE_BOUND = Fraction(174833497030641, 100000000000000)

# Multipliers are deliberately narrow and exact. Values are applied to the
# final Type-2 singleton, all four Type-3 base jobs as one coupled parameter,
# the Type-3 singleton, and the final job.
DEFAULT_MULTIPLIERS = tuple(
    Fraction(1000000 + offset, 1000000)
    for offset in (-1000, -500, -200, -100, 0, 100, 200, 500, 1000)
)
MUTABLE_GROUPS = ((64,), (65, 66, 67, 68), (69,), (70,))


def load_jobs(path):
    with open(path, encoding="utf-8") as handle:
        template = json.load(handle)
    jobs = []
    for layer in template["layers"]:
        for emitted in layer["emit"]:
            jobs.extend([int(emitted["size"])] * int(emitted.get("repeat", 1)))
    for emitted in template.get("final", []):
        jobs.extend([int(emitted["size"])] * int(emitted.get("repeat", 1)))
    return tuple(jobs), int(template["m"])


def scale_job(job, multiplier):
    numerator = job * multiplier.numerator
    denominator = multiplier.denominator
    return max(1, (numerator + denominator // 2) // denominator)


def mutate(base_jobs, multipliers):
    jobs = list(base_jobs)
    for indices, multiplier in zip(MUTABLE_GROUPS, multipliers):
        for index in indices:
            jobs[index] = scale_job(jobs[index], multiplier)
    return tuple(jobs)


def candidate_id(multipliers):
    encoded = ",".join(
        f"{multiplier.numerator}/{multiplier.denominator}"
        for multiplier in multipliers
    )
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def lower_bound_opt(prefix, m):
    """Cheap lower bound on exact offline makespan."""
    return max(max(prefix), math.ceil(sum(prefix) / m))


def online_upper_bound(prefix, m):
    """A feasible online makespan upper bound from list scheduling."""
    loads = [0] * m
    for job in prefix:
        machine = min(range(m), key=loads.__getitem__)
        loads[machine] += job
    return max(loads)


def optimistic_ratio(jobs, m, start=60):
    """Upper bound on what the fixed list-scheduling path can witness.

    This is not a proof that a candidate works. If even this ratio is below the
    target, the candidate is uninteresting for that representative path.
    """
    best = Fraction(0)
    best_prefix = 0
    for length in range(max(1, start), len(jobs) + 1):
        prefix = jobs[:length]
        ratio = Fraction(online_upper_bound(prefix, m), lower_bound_opt(prefix, m))
        if ratio > best:
            best = ratio
            best_prefix = length
    return best, best_prefix


def enumerate_candidates(base_jobs, m, multipliers=DEFAULT_MULTIPLIERS,
                         retain=200):
    baseline_ratio, baseline_prefix = optimistic_ratio(base_jobs, m)
    records = []
    for config in itertools.product(multipliers, repeat=len(MUTABLE_GROUPS)):
        if all(multiplier == 1 for multiplier in config):
            continue
        jobs = mutate(base_jobs, config)
        ratio, prefix = optimistic_ratio(jobs, m)
        records.append({
            "candidate_id": candidate_id(config),
            "multipliers": [
                f"{value.numerator}/{value.denominator}" for value in config
            ],
            "mutable_groups": [list(group) for group in MUTABLE_GROUPS],
            "optimistic_ratio": f"{ratio.numerator}/{ratio.denominator}",
            "optimistic_ratio_decimal": float(ratio),
            "optimistic_prefix": prefix,
            "jobs": [str(job) for job in jobs],
        })
    records.sort(
        key=lambda record: (
            Fraction(record["optimistic_ratio"]),
            record["candidate_id"],
        ),
        reverse=True,
    )
    return {
        "method": "late-interface rational multiplier grid",
        "certifying": False,
        "reason": "cheap representative-path ranking before exact prefix OPT",
        "baseline_bound": str(BASELINE_BOUND),
        "baseline_optimistic_ratio": str(baseline_ratio),
        "baseline_optimistic_prefix": baseline_prefix,
        "grid_size": len(multipliers) ** len(MUTABLE_GROUPS) - 1,
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
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_shortlist.json"))
    parser.add_argument("--retain", type=int, default=200)
    args = parser.parse_args()

    jobs, m = load_jobs(args.seed)
    if m != 5 or len(jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(jobs)}")
    payload = enumerate_candidates(jobs, m, retain=args.retain)
    atomic_json(args.output, payload)
    print(json.dumps({
        "grid_size": payload["grid_size"],
        "retained": payload["retained"],
        "best": payload["candidates"][0] if payload["candidates"] else None,
    }, indent=2))


if __name__ == "__main__":
    main()
