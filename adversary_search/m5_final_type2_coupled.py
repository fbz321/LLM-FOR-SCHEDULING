#!/usr/bin/env python3
"""Probe coupled size changes in Rudin's final Type-2 block.

The five equal B jobs, four equal A jobs, and singleton are controlled by three
exact rational multipliers.  The published suffix remains unchanged.  A basic
OPT lower-bound escape screen removes candidates before exact prefix work.
"""

import argparse
import hashlib
import json
import os
from fractions import Fraction

from m5_late_interface import load_jobs
from m5_two_type3_probe import TARGET, atomic_json, list_escape_screen

HERE = os.path.dirname(os.path.abspath(__file__))
M = 5
DENOMINATOR = 10000
DEFAULT_NUMERATORS = tuple(range(9950, 10051, 5))
GROUPS = ((55, 56, 57, 58, 59), (60, 61, 62, 63), (64,))


def mutate(base_jobs, numerators, denominator=DENOMINATOR):
    if len(numerators) != len(GROUPS):
        raise ValueError("expected three coupled multipliers")
    if denominator <= 0 or any(numerator <= 0 for numerator in numerators):
        raise ValueError("multipliers must be positive")
    jobs = list(base_jobs)
    for group, numerator in zip(GROUPS, numerators):
        for index in group:
            scaled = base_jobs[index] * numerator
            if scaled % denominator:
                raise ValueError("multiplier does not preserve integer job size")
            jobs[index] = scaled // denominator
    return tuple(jobs)


def candidate_id(numerators, denominator=DENOMINATOR):
    encoded = "final-type2:" + ",".join(
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
                config = (b_numerator, a_numerator, singleton_numerator)
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
        "method": "coupled final Type-2 B/A/singleton multiplier grid",
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
        HERE, "results", "m5_structured", "final_type2_coupled_probe.json"))
    parser.add_argument("--survivors", default=os.path.join(
        HERE, "results", "m5_structured", "final_type2_coupled_survivors.json"))
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
