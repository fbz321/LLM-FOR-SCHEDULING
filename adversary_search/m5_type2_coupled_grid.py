#!/usr/bin/env python3
"""Probe coupled B/A/singleton changes in every published Type-2 block.

For one Type-2 stage at a time, the five B jobs, four A jobs, and singleton
receive three exact rational multipliers.  All jobs are globally scaled by the
common denominator, avoiding independent rounding even in the early stages.
A basic-bound scheduler path removes candidates before the complete bounded
threshold game is needed.
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
TYPE2_B_STARTS = (15, 25, 35, 45, 55)


def stage_groups(stage):
    if not 0 <= stage < len(TYPE2_B_STARTS):
        raise ValueError("invalid Type-2 stage")
    start = TYPE2_B_STARTS[stage]
    return (
        tuple(range(start, start + 5)),
        tuple(range(start + 5, start + 9)),
        (start + 9,),
    )


def mutate(base_jobs, stage, numerators, denominator=DENOMINATOR):
    if len(numerators) != 3:
        raise ValueError("expected three coupled multipliers")
    if denominator <= 0 or any(numerator <= 0 for numerator in numerators):
        raise ValueError("multipliers must be positive")
    jobs = [job * denominator for job in base_jobs]
    for group, numerator in zip(stage_groups(stage), numerators):
        for index in group:
            jobs[index] = base_jobs[index] * numerator
    return tuple(jobs)


def candidate_id(stage, numerators, denominator=DENOMINATOR):
    encoded = f"type2-coupled:{stage}:" + ",".join(
        f"{numerator}/{denominator}" for numerator in numerators
    )
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs, numerators=DEFAULT_NUMERATORS,
                         tau=TARGET):
    records = []
    survivors = []
    identity = (DENOMINATOR,) * 3
    for stage in range(len(TYPE2_B_STARTS)):
        for b_numerator in numerators:
            for a_numerator in numerators:
                for singleton_numerator in numerators:
                    config = (
                        b_numerator, a_numerator, singleton_numerator,
                    )
                    if config == identity:
                        continue
                    jobs = mutate(base_jobs, stage, config)
                    screen = list_escape_screen(jobs, M, tau)
                    record = {
                        "candidate_id": candidate_id(stage, config),
                        "stage": stage + 1,
                        "multipliers": [
                            f"{numerator}/{DENOMINATOR}"
                            for numerator in config
                        ],
                        **screen,
                    }
                    if not screen["escaped"]:
                        record["jobs"] = [str(job) for job in jobs]
                        survivors.append(record)
                    records.append(record)
    return {
        "version": 1,
        "method": "coupled Type-2 B/A/singleton multiplier grid",
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
        HERE, "results", "m5_structured", "type2_coupled_grid.json"))
    parser.add_argument("--survivors", default=os.path.join(
        HERE, "results", "m5_structured", "type2_coupled_survivors.json"))
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
