#!/usr/bin/env python3
"""Probe coupled size changes in the three initial five-job blocks.

The first fifteen jobs form three equal-size blocks before the published
Type-2 stages. Each block receives one exact rational multiplier. The complete
sequence is scaled by the common denominator, so no job is rounded.
"""

import argparse
import hashlib
import json
import os

from m5_late_interface import load_jobs
from m5_two_type3_probe import TARGET, atomic_json, list_escape_screen

HERE = os.path.dirname(os.path.abspath(__file__))
M = 5
DENOMINATOR = 10000
DEFAULT_NUMERATORS = tuple(range(9950, 10051, 5))
GROUPS = (
    tuple(range(0, 5)),
    tuple(range(5, 10)),
    tuple(range(10, 15)),
)


def mutate(base_jobs, numerators, denominator=DENOMINATOR):
    if len(numerators) != len(GROUPS):
        raise ValueError("expected three coupled multipliers")
    if denominator <= 0 or any(numerator <= 0 for numerator in numerators):
        raise ValueError("multipliers must be positive")
    jobs = [job * denominator for job in base_jobs]
    for group, numerator in zip(GROUPS, numerators):
        for index in group:
            jobs[index] = base_jobs[index] * numerator
    return tuple(jobs)


def candidate_id(numerators, denominator=DENOMINATOR):
    encoded = "initial-coupled:" + ",".join(
        f"{numerator}/{denominator}" for numerator in numerators
    )
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs, numerators=DEFAULT_NUMERATORS,
                         tau=TARGET):
    records = []
    survivors = []
    identity = (DENOMINATOR,) * len(GROUPS)
    for first in numerators:
        for second in numerators:
            for third in numerators:
                config = (first, second, third)
                if config == identity:
                    continue
                jobs = mutate(base_jobs, config)
                screen = list_escape_screen(jobs, M, tau)
                record = {
                    "candidate_id": candidate_id(config),
                    "multipliers": [
                        f"{numerator}/{DENOMINATOR}" for numerator in config
                    ],
                    **screen,
                }
                if not screen["escaped"]:
                    record["jobs"] = [str(job) for job in jobs]
                    survivors.append(record)
                records.append(record)
    return {
        "version": 1,
        "method": "coupled initial three-block multiplier grid",
        "tau": f"{tau.numerator}/{tau.denominator}",
        "candidate_count": len(records),
        "escaped": len(records) - len(survivors),
        "survivor_count": len(survivors),
        "survivors": survivors,
        "candidates": records,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", default=os.path.join(
        HERE, "seeds", "rudin2001_m5.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "initial_coupled_grid.json"))
    parser.add_argument("--survivors", default=os.path.join(
        HERE, "results", "m5_structured", "initial_coupled_survivors.json"))
    args = parser.parse_args()

    base_jobs, m = load_jobs(args.seed)
    if m != M or len(base_jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(base_jobs)}")
    payload = enumerate_candidates(base_jobs)
    atomic_json(args.output, payload)
    atomic_json(args.survivors, {
        "version": 1,
        "method": payload["method"] + "; basic-LB survivors only",
        "candidate_count": payload["survivor_count"],
        "candidates": payload["survivors"],
    })
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "escaped": payload["escaped"],
        "survivor_count": payload["survivor_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
