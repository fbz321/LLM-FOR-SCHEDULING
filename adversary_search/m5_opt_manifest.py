#!/usr/bin/env python3
"""Build a resumable exact-OPT work manifest for m=5 shortlist candidates."""

import argparse
import json
import os

import incremental_verify as verifier

HERE = os.path.dirname(os.path.abspath(__file__))


def load_content_cache(path):
    """Accept both validated caches and the earlier flat-value search cache."""
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as handle:
        payload = json.load(handle)
    if payload.get("version") != 1:
        raise ValueError("unsupported cache version")
    entries = {}
    for key, entry in payload.get("entries", {}).items():
        if isinstance(entry, dict):
            entries[key] = entry.get("opt")
        else:
            entries[key] = entry
    return entries


def build_manifest(records, m, cached):
    required = {}
    candidate_keys = {}
    for record in records:
        jobs = tuple(int(job) for job in record["jobs"])
        keys = []
        for length in range(1, len(jobs) + 1):
            prefix = jobs[:length]
            key = verifier.prefix_key(m, prefix)
            keys.append(key)
            if key not in cached:
                required.setdefault(key, {
                    "key": key,
                    "m": m,
                    "length": length,
                    "jobs": [str(job) for job in verifier.canonical_prefix(prefix)],
                    "used_by": [],
                })
                required[key]["used_by"].append(record["candidate_id"])
        candidate_keys[record["candidate_id"]] = keys
    jobs = sorted(
        required.values(),
        key=lambda item: (item["length"], item["key"]),
    )
    return {
        "version": 1,
        "method": "content-addressed exact prefix OPT manifest",
        "candidate_count": len(records),
        "cached_prefixes": len(cached),
        "missing_prefixes": len(jobs),
        "jobs": jobs,
        "candidate_keys": candidate_keys,
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
    parser.add_argument("--analysis", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_analysis.json"))
    parser.add_argument("--cache", default=os.path.join(
        HERE, "results", "m5_structured", "prefix_opts_content.json"))
    parser.add_argument("--output", default=os.path.join(
        HERE, "results", "m5_structured", "late_interface_opt_manifest.json"))
    parser.add_argument("--candidates", type=int, default=10)
    args = parser.parse_args()

    with open(args.analysis, encoding="utf-8") as handle:
        analysis = json.load(handle)
    records = analysis["candidates"][:args.candidates]
    cached = load_content_cache(args.cache)
    payload = build_manifest(records, 5, cached)
    atomic_json(args.output, payload)
    print(json.dumps({
        "candidate_count": payload["candidate_count"],
        "cached_prefixes": payload["cached_prefixes"],
        "missing_prefixes": payload["missing_prefixes"],
        "lengths": sorted({job["length"] for job in payload["jobs"]}),
    }, indent=2))


if __name__ == "__main__":
    main()
