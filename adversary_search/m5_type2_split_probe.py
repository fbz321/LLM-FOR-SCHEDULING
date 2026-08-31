#!/usr/bin/env python3
"""Probe 4+1 size splits inside each published Type-2 B block.

One of the five equal B jobs in one Type-2 stage is multiplied by an exact
rational factor k/1000 while every other job is globally multiplied by 1000.
This gives a small structural size surgery without independent rounding.  A
rigorous least-loaded scheduler escape screen rules out candidates whenever its
makespan divided by the basic OPT lower bound stays below the target.
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
TYPE2_B_STARTS = (15, 25, 35, 45, 55)
DEFAULT_NUMERATORS = tuple(
    numerator for numerator in range(900, 1101) if numerator != 1000
)
DENOMINATOR = 1000


def split_candidate(base_jobs, stage, position, numerator,
                    denominator=DENOMINATOR):
    if not 0 <= stage < len(TYPE2_B_STARTS):
        raise ValueError("invalid Type-2 stage")
    if not 0 <= position < 5:
        raise ValueError("invalid position")
    if numerator <= 0 or denominator <= 0 or numerator == denominator:
        raise ValueError("invalid non-identity multiplier")
    jobs = [job * denominator for job in base_jobs]
    index = TYPE2_B_STARTS[stage] + position
    jobs[index] = base_jobs[index] * numerator
    if any(job <= 0 for job in jobs):
        raise ValueError("job sizes must be positive")
    return tuple(jobs)


def candidate_id(stage, position, numerator, denominator=DENOMINATOR):
    encoded = f"type2-b-split:{stage}:{position}:{numerator}/{denominator}"
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs, numerators=DEFAULT_NUMERATORS,
                         tau=TARGET):
    records = []
    survivors = []
    for stage in range(len(TYPE2_B_STARTS)):
        for position in range(5):
            for numerator in numerators:
                jobs = split_candidate(base_jobs, stage, position, numerator)
                screen = list_escape_screen(jobs, M, tau)
                record = {
                    "candidate_id": candidate_id(
                        stage, position, numerator,
                    ),
                    "stage": stage + 1,
                    "position": position,
                    "multiplier": f"{numerator}/{DENOMINATOR}",
                    **screen,
                }
                if not screen["escaped"]:
                    record["jobs"] = [str(job) for job in jobs]
                    survivors.append(record)
                records.append(record)
    return {
        "version": 1,
        "method": "single-job 4+1 size split in Type-2 B blocks",
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
        HERE, "results", "m5_structured", "type2_split_probe.json"))
    args = parser.parse_args()

    base_jobs, m = load_jobs(args.seed)
    if m != M or len(base_jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(base_jobs)}")
    payload = enumerate_candidates(base_jobs)
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "escaped": payload["escaped"],
        "survivor_count": payload["survivor_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
