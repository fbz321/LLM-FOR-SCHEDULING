#!/usr/bin/env python3
"""Enumerate every terminal order of Rudin's four A jobs, singleton, and final job."""

import argparse
import hashlib
import itertools
import json
import os

from m5_late_interface import load_jobs

HERE = os.path.dirname(os.path.abspath(__file__))
TERMINAL_START = 65


def unique_terminal_orders(base_jobs):
    terminal = base_jobs[TERMINAL_START:]
    if len(terminal) != 6 or len(set(terminal)) != 3:
        raise ValueError("unexpected Rudin terminal multiset")
    orders = sorted(set(itertools.permutations(terminal)))
    if len(orders) != 30:
        raise ValueError(f"expected 30 terminal orders, got {len(orders)}")
    return orders


def order_id(base_jobs, order):
    labels = []
    a = base_jobs[65]
    singleton = base_jobs[69]
    final = base_jobs[70]
    for job in order:
        labels.append("A" if job == a else "S" if job == singleton else "F")
    encoded = "".join(labels)
    return encoded, hashlib.sha256(encoded.encode("ascii")).hexdigest()[:16]


def enumerate_candidates(base_jobs):
    records = []
    for order in unique_terminal_orders(base_jobs):
        label, candidate_id = order_id(base_jobs, order)
        records.append({
            "candidate_id": candidate_id,
            "order": label,
            "jobs": [str(job) for job in base_jobs[:TERMINAL_START] + order],
        })
    return {
        "version": 1,
        "method": "all unique orders of terminal multiset AAAASF",
        "candidate_count": len(records),
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
        HERE, "results", "m5_structured", "terminal_orders.json"))
    args = parser.parse_args()

    jobs, m = load_jobs(args.seed)
    if m != 5 or len(jobs) != 71:
        raise ValueError(f"unexpected seed shape m={m}, jobs={len(jobs)}")
    payload = enumerate_candidates(jobs)
    atomic_json(args.output, payload)
    print(json.dumps({"candidate_count": payload["candidate_count"]}, indent=2))


if __name__ == "__main__":
    main()
