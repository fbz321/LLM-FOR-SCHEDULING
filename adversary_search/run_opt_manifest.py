#!/usr/bin/env python3
"""Execute a content-addressed exact-OPT manifest with resumable output.

The manifest is deterministic and each completed result is written atomically.
Jobs with matching basic lower and LPT upper bounds are solved without opening
worker processes. Remaining jobs use ``parallel_opt.exact_opt``. The executor
can shard work across several independent processes via ``--shard``.
"""

import argparse
import json
import os
import time
from concurrent.futures import ProcessPoolExecutor, as_completed

from parallel_opt import basic_lower_bound, exact_opt, lpt_upper_bound

HERE = os.path.dirname(os.path.abspath(__file__))


def atomic_json(path, payload):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    temporary = path + ".tmp"
    with open(temporary, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def load_results(path):
    if not os.path.exists(path):
        return {"version": 1, "entries": {}}
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("version") != 1 or not isinstance(payload.get("entries"), dict):
        raise ValueError("unsupported result cache")
    return payload


def select_jobs(manifest, results, shard_index=0, shard_count=1,
                min_length=0, max_length=None, limit=None):
    if shard_count <= 0 or not 0 <= shard_index < shard_count:
        raise ValueError("invalid shard")
    selected = []
    for item in manifest["jobs"]:
        if item["key"] in results["entries"]:
            continue
        if item["length"] < min_length:
            continue
        if max_length is not None and item["length"] > max_length:
            continue
        if int(item["key"], 16) % shard_count != shard_index:
            continue
        selected.append(item)
    selected.sort(key=lambda item: (-item["length"], item["key"]))
    return selected if limit is None else selected[:limit]


def bound_profile(items):
    records = []
    for item in items:
        jobs = tuple(int(job) for job in item["jobs"])
        lower = basic_lower_bound(jobs, int(item["m"]))
        upper = lpt_upper_bound(jobs, int(item["m"]))
        records.append({
            "key": item["key"],
            "length": item["length"],
            "lower_bound": str(lower),
            "lpt_upper_bound": str(upper),
            "gap": str(upper - lower),
            "matching": lower == upper,
        })
    return records


def solve_item(item, workers, split_depth):
    jobs = tuple(int(job) for job in item["jobs"])
    m = int(item["m"])
    from incremental_verify import prefix_key
    if prefix_key(m, jobs) != item["key"]:
        raise ValueError(f"manifest content key mismatch: {item['key']}")
    started = time.time()
    lower = basic_lower_bound(jobs, m)
    upper = lpt_upper_bound(jobs, m)
    if lower == upper:
        optimum = lower
        decisions = 0
        method = "matching-bounds"
    else:
        result = exact_opt(
            jobs, m, workers=workers, split_depth=split_depth,
        )
        optimum = result.optimum
        lower = result.lower_bound
        upper = result.lpt_upper_bound
        decisions = result.decisions
        method = "parallel-decision-search"
    return {
        "key": item["key"],
        "m": m,
        "length": int(item["length"]),
        "jobs": item["jobs"],
        "opt": str(optimum),
        "lower_bound": str(lower),
        "lpt_upper_bound": str(upper),
        "decisions": decisions,
        "method": method,
        "workers": workers,
        "split_depth": split_depth,
        "seconds": time.time() - started,
    }


def run(manifest, output, workers, split_depth, outer_jobs=1,
        shard_index=0, shard_count=1, min_length=0, max_length=None,
        limit=None):
    results = load_results(output)
    selected = select_jobs(
        manifest, results, shard_index=shard_index, shard_count=shard_count,
        min_length=min_length, max_length=max_length, limit=limit,
    )
    if not selected:
        return results, {"selected": 0, "completed": 0}

    # Avoid nested oversubscription. ``workers`` is the total process budget;
    # each outer job receives a disjoint share of it.
    outer_jobs = max(1, min(outer_jobs, len(selected), workers))
    inner_workers = max(1, workers // outer_jobs)
    completed = 0

    if outer_jobs == 1:
        for item in selected:
            result = solve_item(item, inner_workers, split_depth)
            results["entries"][result["key"]] = result
            atomic_json(output, results)
            completed += 1
            print(
                f"OPT {completed}/{len(selected)} length={result['length']} "
                f"method={result['method']} seconds={result['seconds']:.1f}",
                flush=True,
            )
    else:
        with ProcessPoolExecutor(max_workers=outer_jobs) as executor:
            futures = {
                executor.submit(solve_item, item, inner_workers, split_depth): item
                for item in selected
            }
            for future in as_completed(futures):
                result = future.result()
                results["entries"][result["key"]] = result
                atomic_json(output, results)
                completed += 1
                print(
                    f"OPT {completed}/{len(selected)} length={result['length']} "
                    f"method={result['method']} seconds={result['seconds']:.1f}",
                    flush=True,
                )
    return results, {
        "selected": len(selected),
        "completed": completed,
        "outer_jobs": outer_jobs,
        "inner_workers": inner_workers,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_opt_manifest.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_opt_results.json"))
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 1,
                        help="total process budget")
    parser.add_argument("--outer-jobs", type=int, default=4,
                        help="concurrent prefixes within total process budget")
    parser.add_argument("--split-depth", type=int, default=9)
    parser.add_argument("--shard", default="0/1",
                        help="deterministic shard INDEX/COUNT")
    parser.add_argument("--min-length", type=int, default=0)
    parser.add_argument("--max-length", type=int)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--profile-bounds", action="store_true")
    args = parser.parse_args()

    shard_index, shard_count = (int(part) for part in args.shard.split("/", 1))
    with open(args.manifest, encoding="utf-8") as handle:
        manifest = json.load(handle)
    results = load_results(args.output)
    selected = select_jobs(
        manifest, results, shard_index=shard_index, shard_count=shard_count,
        min_length=args.min_length, max_length=args.max_length,
        limit=args.limit,
    )
    if args.dry_run:
        payload = {
            "selected": len(selected),
            "length_counts": {
                str(length): sum(item["length"] == length for item in selected)
                for length in sorted({item["length"] for item in selected})
            },
            "workers": args.workers,
            "outer_jobs": args.outer_jobs,
            "shard": args.shard,
        }
        if args.profile_bounds:
            profile = bound_profile(selected)
            payload["matching_bounds"] = sum(
                record["matching"] for record in profile
            )
            payload["nonmatching_bounds"] = sum(
                not record["matching"] for record in profile
            )
            payload["profile"] = profile
        print(json.dumps(payload, indent=2))
        return

    _, summary = run(
        manifest, args.output, args.workers, args.split_depth,
        outer_jobs=args.outer_jobs, shard_index=shard_index,
        shard_count=shard_count, min_length=args.min_length,
        max_length=args.max_length, limit=args.limit,
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
