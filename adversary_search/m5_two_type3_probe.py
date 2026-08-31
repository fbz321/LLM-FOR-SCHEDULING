#!/usr/bin/env python3
"""Probe a conservative two-Type-3-shaped extension of Rudin Table A2.

The dissertation does not publish enough state and packing information to
reconstruct a certified two-Type-3 recurrence for m=5.  This module therefore
makes a narrower claim: it inserts an exact rationally scaled copy of the
published five-job Type-3 block and tests the resulting explicit finite
sequences.  It must not be described as a formula-derived Rudin construction.

For q = p/r > 1, the inserted block is the published block divided by q and is
placed immediately before the published block.  To avoid rounding, the entire
published sequence is multiplied by p while the inserted block is multiplied
by r.  Competitive ratios are invariant under this common scaling.
"""

import argparse
import hashlib
import json
import math
import os
from fractions import Fraction

from m5_late_interface import load_jobs

HERE = os.path.dirname(os.path.abspath(__file__))
M = 5
TYPE3_START = 65
TYPE3_STOP = 70
TARGET = Fraction(1748334970307, 1000000000000)
DEFAULT_Q = tuple(Fraction(numerator, 1000) for numerator in range(1001, 1101))


def candidate_id(q):
    encoded = f"scaled-copy-before:{q.numerator}/{q.denominator}"
    return hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def insert_scaled_type3(base_jobs, q):
    """Return an integer sequence encoding an inserted block divided by q."""
    q = Fraction(q)
    if q <= 1:
        raise ValueError("q must be greater than one")
    if len(base_jobs) != 71:
        raise ValueError(f"expected 71 baseline jobs, got {len(base_jobs)}")
    numerator, denominator = q.numerator, q.denominator
    prefix = tuple(job * numerator for job in base_jobs[:TYPE3_START])
    inserted = tuple(
        job * denominator for job in base_jobs[TYPE3_START:TYPE3_STOP]
    )
    suffix = tuple(job * numerator for job in base_jobs[TYPE3_START:])
    jobs = prefix + inserted + suffix
    if len(jobs) != 76 or any(job <= 0 for job in jobs):
        raise ValueError("invalid scaled-copy candidate")
    return jobs


def basic_opt_lower_bound(prefix, m):
    return max(max(prefix), math.ceil(sum(prefix) / m))


def list_escape_screen(jobs, m, tau):
    """Test one scheduler path using a rigorous lower bound on every OPT.

    For the deterministic least-loaded-machine path, M/OPT <= M/LB because
    LB <= OPT.  Thus max(M/LB) < tau certifies an escape from the threshold
    game without computing any exact candidate-specific OPT values.
    """
    loads = [0] * m
    maximum = Fraction(0)
    maximum_prefix = 0
    for length, job in enumerate(jobs, 1):
        machine = min(range(m), key=lambda index: (loads[index], index))
        loads[machine] += job
        upper = Fraction(max(loads), basic_opt_lower_bound(jobs[:length], m))
        if upper > maximum:
            maximum = upper
            maximum_prefix = length
    return {
        "escaped": maximum < tau,
        "path_ratio_upper": f"{maximum.numerator}/{maximum.denominator}",
        "path_ratio_upper_decimal": float(maximum),
        "maximum_prefix": maximum_prefix,
        "final_loads": [str(load) for load in sorted(loads)],
    }


def enumerate_candidates(base_jobs, q_values=DEFAULT_Q, tau=TARGET):
    records = []
    for q in q_values:
        q = Fraction(q)
        jobs = insert_scaled_type3(base_jobs, q)
        screen = list_escape_screen(jobs, M, tau)
        record = {
            "candidate_id": candidate_id(q),
            "q": f"{q.numerator}/{q.denominator}",
            "job_count": len(jobs),
            **screen,
        }
        if not screen["escaped"]:
            record["jobs"] = [str(job) for job in jobs]
        records.append(record)
    survivors = [record for record in records if not record["escaped"]]
    return {
        "version": 1,
        "method": "exact rational scaled Type-3 copy before published block",
        "certifying_construction": False,
        "construction_warning": (
            "The inserted block is Type-3-shaped only. The dissertation does "
            "not provide the two-layer state transitions and packing proof "
            "needed to call it a Rudin Type-3 recurrence."
        ),
        "screen": (
            "deterministic list-scheduling escape path with basic exact OPT "
            "lower bounds"
        ),
        "tau": f"{tau.numerator}/{tau.denominator}",
        "candidate_count": len(records),
        "escaped": len(records) - len(survivors),
        "survivor_count": len(survivors),
        "survivors": survivors,
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
    parser.add_argument("--seed", default=os.path.join(
        HERE, "seeds", "rudin2001_m5.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "two_type3_scaled_probe.json"))
    parser.add_argument("--q-start", type=int, default=1001)
    parser.add_argument("--q-stop", type=int, default=1100)
    parser.add_argument("--q-denominator", type=int, default=1000)
    args = parser.parse_args()

    if args.q_denominator <= 0 or args.q_start > args.q_stop:
        raise ValueError("invalid q grid")
    q_values = tuple(
        Fraction(numerator, args.q_denominator)
        for numerator in range(args.q_start, args.q_stop + 1)
    )
    if any(q <= 1 for q in q_values):
        raise ValueError("every q value must be greater than one")
    base_jobs, m = load_jobs(args.seed)
    if m != M:
        raise ValueError(f"expected m={M}, got {m}")
    payload = enumerate_candidates(base_jobs, q_values=q_values)
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "escaped": payload["escaped"],
        "survivor_count": payload["survivor_count"],
    }, indent=2))


if __name__ == "__main__":
    main()
