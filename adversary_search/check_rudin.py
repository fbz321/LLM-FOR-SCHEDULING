#!/usr/bin/env python3
"""Validate a fixed Rudin 2001 sequence with exact prefix OPT values.

The cache is resumable. Use --cache-only to refuse missing prefix computation; a
complete cache still proceeds to the exact adversarial check.
"""
import json, os, sys, time, threading
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema
from m4_search import opt
from fractions import Fraction

import argparse
_ap = argparse.ArgumentParser()
_ap.add_argument('--seed', required=True)
_ap.add_argument('--tau', required=True)
_ap.add_argument('--cache', required=True)
_ap.add_argument("--cache-only", action="store_true",
                 help="do not compute missing prefix OPT values")
_A = _ap.parse_args()
SEED = _A.seed if os.path.isabs(_A.seed) else os.path.join(os.path.dirname(os.path.abspath(__file__)), _A.seed)
CACHE = _A.cache
TAU = Fraction(_A.tau)

def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)

tpl = json.load(open(SEED, encoding='utf-8'))
sizes, meta = template_schema.materialize(tpl)
m = meta['m']
L = 1
import math
for s in sizes:
    L = math.lcm(L, s.denominator)
jobs = [int(s * L) for s in sizes]
n = len(jobs)
log(f"jobs={n} m={m} tau={TAU}")

# ---------- Phase 1: prefix OPTs with disk cache ----------
cache = {}
if os.path.exists(CACHE):
    cache = json.load(open(CACHE))
    log(f"cache loaded: {len(cache)} entries")

expected_keys = {str(i) for i in range(1, n + 1)}
extra_keys = set(cache) - expected_keys
if extra_keys:
    raise ValueError(f"cache has unexpected prefix keys: {sorted(extra_keys)}")
missing = sorted(int(k) for k in expected_keys - set(cache))
if missing and _A.cache_only:
    log(f"PARTIAL: cached={len(cache)}/{n}; missing={missing}")
    print(f"RESULT: PARTIAL cached={len(cache)}/{n} missing={missing}", flush=True)
    raise SystemExit(2)

def save_cache():
    tmp = CACHE + '.tmp'
    json.dump(cache, open(tmp, 'w'))
    os.replace(tmp, CACHE)

for i in range(1, n + 1):
    if str(i) in cache:
        continue
    t0 = time.time()
    v = opt(tuple(jobs[:i]), m)
    cache[str(i)] = str(v)
    save_cache()
    log(f"OPT(prefix {i:2d}) done ({time.time()-t0:.1f}s)")

opt_pref = [0] * (n + 1)
for i in range(1, n + 1):
    opt_pref[i] = int(cache[str(i)])
log("Phase 1 complete")

# ---------- Phase 2: check recursion with progress ----------
tn, td = TAU.numerator, TAU.denominator
sys.setrecursionlimit(100000)
memo = {}
viol = set()
stats = {'calls': 0}
stop = {'res': None, 'witness': None}

def progress():
    while stop['res'] is None:
        time.sleep(60)
        if stop['res'] is None:
            log(f"  progress: memo={len(memo)} viol={len(viol)} calls={stats['calls']}")

th = threading.Thread(target=progress, daemon=True)
th.start()

def W(i, loads):
    key = (i, loads)
    hit = memo.get(key)
    if hit is not None:
        return hit
    stats['calls'] += 1
    if opt_pref[i] > 0 and max(loads) * td >= tn * opt_pref[i]:
        memo[key] = True
        viol.add(key)
        return True
    if i == n:
        memo[key] = False
        return False
    p = jobs[i]
    seen = set()
    ok = True
    witness_j = None
    for j in range(m):
        l = loads[j]
        if l in seen:
            continue
        seen.add(l)
        nl = list(loads)
        nl[j] = l + p
        if not W(i + 1, tuple(sorted(nl))):
            ok = False
            witness_j = j
            break
    memo[key] = ok
    if not ok and stop['witness'] is None:
        stop['witness'] = (key, witness_j)
    return ok

t0 = time.time()
res = W(0, (0,) * m)
stop['res'] = res
dt = time.time() - t0
log(f"Phase 2 done: {'PASS' if res else 'FAIL'} ({dt:.1f}s, memo={len(memo)}, viol={len(viol)}, calls={stats['calls']})")

if not res and stop['witness']:
    (wi, wloads), wj = stop['witness']
    log(f"首个逃逸状态: i={wi} loads={wloads} (第 {wj} 台机放置后进入败局)")
    # 重建见证路径
    path = []
    i, loads = 0, (0,) * m
    while i < wi:
        p = jobs[i]
        for j in range(m):
            nl = list(loads); nl[j] += p
            nk = (i + 1, tuple(sorted(nl)))
            if memo.get(nk) is False:
                path.append((i, p, loads[j], loads[j] + p))
                loads = tuple(sorted(nl)); i += 1
                break
        else:
            break
    log("见证路径 (job#, size, 机器原载, 新载):")
    for row in path:
        log(f"  job{row[0]:2d} size={row[1]} : {row[2]} -> {row[3]}")

print(f"RESULT: {'PASS' if res else 'FAIL'} tau={TAU} states={len(memo)} viol={len(viol)} time={dt:.1f}s", flush=True)