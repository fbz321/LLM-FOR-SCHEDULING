#!/usr/bin/env python3
"""Exact process-parallel makespan optimization on identical machines.

The search sorts jobs by decreasing size, removes machine-label symmetry, and
splits the first ``split_depth`` placement levels into disjoint canonical
states.  Each state is then checked independently by a worker process.
"""

import argparse
import json
import math
import multiprocessing as mp
import os
import sys
import time
from dataclasses import asdict, dataclass


_WORK_JOBS = ()
_WORK_CAP = 0


@dataclass(frozen=True)
class OptimizationResult:
    optimum: int
    lower_bound: int
    lpt_upper_bound: int
    decisions: int


def _validate(jobs, m):
    if m <= 0:
        raise ValueError("m must be positive")
    normalized = tuple(sorted((int(p) for p in jobs), reverse=True))
    if any(p <= 0 for p in normalized):
        raise ValueError("job sizes must be positive integers")
    return normalized


def lpt_upper_bound(jobs, m):
    """Return the makespan produced by longest-processing-time-first."""
    jobs = _validate(jobs, m)
    if not jobs:
        return 0
    loads = [0] * m
    for p in jobs:
        j = min(range(m), key=loads.__getitem__)
        loads[j] += p
    return max(loads)


def basic_lower_bound(jobs, m):
    """Return max(largest job, ceiling of average machine load)."""
    jobs = _validate(jobs, m)
    if not jobs:
        return 0
    return max(jobs[0], (sum(jobs) + m - 1) // m)


def feasible_state(jobs, initial_loads, cap):
    """Check one capacity-constrained subtree exactly."""
    jobs = tuple(jobs)
    loads = list(initial_loads)
    if any(load > cap for load in loads):
        return False

    remaining = sum(jobs)
    m = len(loads)

    def dfs(i):
        nonlocal remaining
        if i == len(jobs):
            return True
        if m * cap - sum(loads) < remaining:
            return False

        p = jobs[i]
        remaining -= p
        seen = set()
        for j in range(m):
            old = loads[j]
            if old in seen or old + p > cap:
                continue
            seen.add(old)
            loads[j] = old + p
            if dfs(i + 1):
                loads[j] = old
                remaining += p
                return True
            loads[j] = old
            # All empty machines are equivalent at this node.
            if old == 0:
                break

        remaining += p
        return False

    return dfs(0)


def build_frontier(jobs, m, split_depth, cap):
    """Enumerate canonical placements of the first jobs that respect cap."""
    if split_depth < 0:
        raise ValueError("split_depth must be nonnegative")
    states = {(0,) * m}
    for p in jobs[:split_depth]:
        next_states = set()
        for state in states:
            seen = set()
            for j, load in enumerate(state):
                if load in seen or load + p > cap:
                    continue
                seen.add(load)
                updated = list(state)
                updated[j] += p
                next_states.add(tuple(sorted(updated)))
        states = next_states
        if not states:
            break
    return tuple(sorted(states))


def _init_worker(jobs, cap):
    global _WORK_JOBS, _WORK_CAP
    _WORK_JOBS = jobs
    _WORK_CAP = cap


def _check_worker(state):
    return feasible_state(_WORK_JOBS, state, _WORK_CAP)


def schedule_feasible(jobs, m, cap, workers=1, split_depth=0):
    """Return whether all jobs fit on ``m`` machines with makespan ``cap``."""
    jobs = _validate(jobs, m)
    if workers <= 0:
        raise ValueError("workers must be positive")
    if split_depth < 0:
        raise ValueError("split_depth must be nonnegative")
    if not jobs:
        return True
    if cap < basic_lower_bound(jobs, m):
        return False

    depth = min(split_depth, len(jobs))
    frontier = build_frontier(jobs, m, depth, cap)
    if not frontier:
        return False
    rest = jobs[depth:]

    if workers == 1 or len(frontier) == 1:
        return any(feasible_state(rest, state, cap) for state in frontier)

    method = "fork" if "fork" in mp.get_all_start_methods() else "spawn"
    ctx = mp.get_context(method)
    process_count = min(workers, len(frontier))
    with ctx.Pool(process_count, initializer=_init_worker,
                  initargs=(rest, cap)) as pool:
        for feasible in pool.imap_unordered(_check_worker, frontier, chunksize=1):
            if feasible:
                pool.terminate()
                return True
    return False


def exact_opt(jobs, m, workers=1, split_depth=0):
    """Compute exact minimum makespan using parallel decision searches."""
    jobs = _validate(jobs, m)
    if workers <= 0:
        raise ValueError("workers must be positive")
    if split_depth < 0:
        raise ValueError("split_depth must be nonnegative")
    if not jobs:
        return OptimizationResult(0, 0, 0, 0)

    initial_lower = basic_lower_bound(jobs, m)
    initial_upper = lpt_upper_bound(jobs, m)
    lower, upper = initial_lower, initial_upper
    decisions = 0

    while lower < upper:
        cap = (lower + upper) // 2
        decisions += 1
        if schedule_feasible(jobs, m, cap, workers, split_depth):
            upper = cap
        else:
            lower = cap + 1

    return OptimizationResult(lower, initial_lower, initial_upper, decisions)


def _load_jobs(seed, prefix):
    project_dir = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, project_dir)
    import template_schema

    with open(seed, encoding="utf-8") as handle:
        template = json.load(handle)
    sizes, metadata = template_schema.materialize(template)
    if prefix is None:
        prefix = len(sizes)
    if prefix < 1 or prefix > len(sizes):
        raise ValueError(f"prefix must be between 1 and {len(sizes)}")

    scale = 1
    for size in sizes:
        scale = math.lcm(scale, size.denominator)
    jobs = tuple(int(size * scale) for size in sizes[:prefix])
    return jobs, metadata["m"], prefix, scale


def main():
    parser = argparse.ArgumentParser(
        description="Compute an exact prefix OPT using multiple processes")
    parser.add_argument("--seed", required=True)
    parser.add_argument("--prefix", type=int)
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--split-depth", type=int, default=9)
    parser.add_argument("--output", help="optional JSON result path")
    args = parser.parse_args()

    jobs, m, prefix, scale = _load_jobs(args.seed, args.prefix)
    started = time.time()
    result = exact_opt(jobs, m, args.workers, args.split_depth)
    payload = asdict(result)
    payload.update({
        "prefix": prefix,
        "jobs": len(jobs),
        "machines": m,
        "scale": str(scale),
        "workers": args.workers,
        "split_depth": args.split_depth,
        "seconds": time.time() - started,
    })
    # JSON numbers can lose precision in downstream JavaScript tools.
    for key in ("optimum", "lower_bound", "lpt_upper_bound"):
        payload[key] = str(payload[key])

    if args.output:
        temporary = args.output + ".tmp"
        with open(temporary, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
        os.replace(temporary, args.output)

    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
