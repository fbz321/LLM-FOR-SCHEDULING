#!/usr/bin/env python3
"""Pilot an additional Type-2-shaped block before the published Type-3 block.

A rationally scaled copy of the final published Type-2 ten-job block (five B,
four A, singleton) is inserted immediately before the Type-3 block. This is an
explicit fixed-sequence family, not a formula-derived sixth Type-2 layer: the
new block does not reconstruct downstream sizes or claim Rudin's tableau
packing proof. Exact OPT/game verification remains the final arbiter.
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
INSERT_AT = 65
COPY_START = 55
COPY_STOP = 65
DEFAULT_Q = tuple(Fraction(numerator, 1000) for numerator in range(1200, 2001))


def insert_scaled_type2(base_jobs, q):
    """Insert a copy whose size relative to the published sequence is ``1/q``."""
    q = Fraction(q)
    if q <= 0:
        raise ValueError("q must be positive")
    numerator, denominator = q.numerator, q.denominator
    prefix = tuple(job * numerator for job in base_jobs[:INSERT_AT])
    inserted = tuple(
        job * denominator for job in base_jobs[COPY_START:COPY_STOP]
    )
    suffix = tuple(job * numerator for job in base_jobs[INSERT_AT:])
    jobs = prefix + inserted + suffix
    if len(jobs) != 81 or any(job <= 0 for job in jobs):
        raise ValueError("invalid scaled-copy candidate")
    return jobs


def candidate_id(q):
    q = Fraction(q)
    encoded = f"inserted-type2-copy:{q.numerator}/{q.denominator}"
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs, q_values=DEFAULT_Q, tau=TARGET):
    records = []
    survivors = []
    for q in q_values:
        q = Fraction(q)
        jobs = insert_scaled_type2(base_jobs, q)
        screen = list_escape_screen(jobs, M, tau)
        record = {
            "candidate_id": candidate_id(q),
            "q": f"{q.numerator}/{q.denominator}",
            "inserted_relative_scale": f"{q.denominator}/{q.numerator}",
            "job_count": len(jobs),
            **screen,
        }
        if not screen["escaped"]:
            record["jobs"] = [str(job) for job in jobs]
            survivors.append(record)
        records.append(record)
    return {
        "version": 1,
        "method": "scaled final-Type-2 block copy inserted before Type-3",
        "certifying_construction": False,
        "construction_warning": (
            "This is Type-2-shaped only: downstream formulas and the tableau "
            "packing proof are not re-derived. It is an explicit sequence "
            "search family whose survivors require exact verification."
        ),
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
        HERE, "results", "m5_structured", "inserted_type2_probe.json"))
    parser.add_argument("--survivors", default=os.path.join(
        HERE, "results", "m5_structured", "inserted_type2_survivors.json"))
    parser.add_argument("--q-start", type=int, default=1200)
    parser.add_argument("--q-stop", type=int, default=2000)
    parser.add_argument("--q-denominator", type=int, default=1000)
    args = parser.parse_args()

    if args.q_denominator <= 0 or args.q_start > args.q_stop:
        raise ValueError("invalid q grid")
    q_values = tuple(
        Fraction(numerator, args.q_denominator)
        for numerator in range(args.q_start, args.q_stop + 1)
    )
    base_jobs, m = load_jobs(args.seed)
    if m != M or len(base_jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(base_jobs)}")
    payload = enumerate_candidates(base_jobs, q_values=q_values)
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
