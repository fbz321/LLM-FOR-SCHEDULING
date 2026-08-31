#!/usr/bin/env python3
"""Probe one shared B/A/singleton perturbation across all Type-2 stages.

Unlike the one-stage grids, this family changes all five Type-2 stages
simultaneously with one shared triple of exact multipliers. This is a small
coordinated proxy for changing the repeated layer mechanism, while retaining
the published multiplicities, Type-3 block, and final job.
"""

import argparse
import hashlib
import json
import os

from m5_late_interface import load_jobs
from m5_two_type3_probe import TARGET, atomic_json, list_escape_screen
from m5_type2_coupled_grid import TYPE2_B_STARTS

HERE = os.path.dirname(os.path.abspath(__file__))
M = 5
DENOMINATOR = 10000
DEFAULT_NUMERATORS = tuple(range(9950, 10051, 5))


def groups():
    result = [[], [], []]
    for start in TYPE2_B_STARTS:
        result[0].extend(range(start, start + 5))
        result[1].extend(range(start + 5, start + 9))
        result[2].append(start + 9)
    return tuple(tuple(group) for group in result)


GROUPS = groups()


def mutate(base_jobs, numerators, denominator=DENOMINATOR):
    if len(numerators) != len(GROUPS):
        raise ValueError("expected three shared multipliers")
    if denominator <= 0 or any(numerator <= 0 for numerator in numerators):
        raise ValueError("multipliers must be positive")
    jobs = [job * denominator for job in base_jobs]
    for group, numerator in zip(GROUPS, numerators):
        for index in group:
            jobs[index] = base_jobs[index] * numerator
    return tuple(jobs)


def candidate_id(numerators, denominator=DENOMINATOR):
    encoded = "all-type2-shared:" + ",".join(
        f"{numerator}/{denominator}" for numerator in numerators
    )
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs, numerators=DEFAULT_NUMERATORS,
                         tau=TARGET):
    records = []
    survivors = []
    identity = (DENOMINATOR,) * len(GROUPS)
    for b_numerator in numerators:
        for a_numerator in numerators:
            for singleton_numerator in numerators:
                config = (
                    b_numerator, a_numerator, singleton_numerator,
                )
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
        "method": "shared B/A/singleton multipliers across all Type-2 stages",
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
        HERE, "results", "m5_structured", "all_type2_shared_grid.json"))
    parser.add_argument("--survivors", default=os.path.join(
        HERE, "results", "m5_structured", "all_type2_shared_survivors.json"))
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
