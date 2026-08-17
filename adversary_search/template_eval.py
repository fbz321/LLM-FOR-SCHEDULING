#!/usr/bin/env python3
"""模板约束求值器（A3'/C0）。

对抗者的作业序列由模板（JSON，见 SCHEMA.md）完全固定，只有调度器分支：
  精确模式  值 = min_调度器 max_前缀 makespan/OPT（真下界语义）
  阈值模式  --check tau：验证 值 >= tau（早停剪枝，快几个量级；
            违规状态集 = 强制证书雏形，C1 GameTree 叶子）

模板展开由 template_schema.materialize 完成（参数/解方程/递推/循环）。
种子模板在 seeds/（FKT、Braun r=1、Rudin，均已冒烟通过）。

用法：
  python template_eval.py --seed fkt
  python template_eval.py --seed braun --check 1.7310194
  python template_eval.py --seed rudin --eps 0.01 --check 1.7220508
  python template_eval.py --template my_template.json [--check tau]
  python template_eval.py --jobs 207,207,207,207,500,500,500,500,1000
"""

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m4_search import opt  # 精确 OPT（分支定界枚举，lru_cache）
import template_schema

SEED_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "seeds")


def _to_int_jobs(sizes):
    L = 1
    for s in sizes:
        L = math.lcm(L, s.denominator)
    jobs = tuple(int(s * L) for s in sizes)
    assert all(p > 0 for p in jobs), "非正作业尺寸"
    return jobs


def _prefix_opts(jobs, m):
    n = len(jobs)
    opt_pref = [0] * (n + 1)
    for i in range(1, n + 1):
        opt_pref[i] = opt(tuple(jobs[:i]), m)
    return opt_pref


def eval_sequence(sizes, m=4):
    """精确值 = min_调度器 max_前缀 makespan/OPT。返回 (值, 状态数)。"""
    jobs = _to_int_jobs(sizes)
    n = len(jobs)
    opt_pref = _prefix_opts(jobs, m)
    sys.setrecursionlimit(100000)
    memo = {}

    def V(i, loads):
        key = (i, loads)
        hit = memo.get(key)
        if hit is not None:
            return hit
        r = Fraction(max(loads), opt_pref[i]) if opt_pref[i] > 0 else Fraction(0)
        if i == n:
            memo[key] = r
            return r
        p = jobs[i]
        best = None
        seen = set()
        for j in range(m):
            l = loads[j]
            if l in seen:
                continue
            seen.add(l)
            nl = list(loads)
            nl[j] = l + p
            v = V(i + 1, tuple(sorted(nl)))
            if best is None or v < best:
                best = v
        val = r if r > best else best
        memo[key] = val
        return val

    val = V(0, (0,) * m)
    return val, len(memo)


def check_sequence(sizes, tau, m=4):
    """阈值模式：验证 值 >= tau（Fraction）。返回 (通过?, 状态数, 违规状态数)。"""
    jobs = _to_int_jobs(sizes)
    n = len(jobs)
    opt_pref = _prefix_opts(jobs, m)
    tn, td = tau.numerator, tau.denominator
    sys.setrecursionlimit(100000)
    memo = {}
    viol = set()

    def W(i, loads):
        key = (i, loads)
        hit = memo.get(key)
        if hit is not None:
            return hit
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
        for j in range(m):
            l = loads[j]
            if l in seen:
                continue
            seen.add(l)
            nl = list(loads)
            nl[j] = l + p
            if not W(i + 1, tuple(sorted(nl))):
                ok = False
                break
        memo[key] = ok
        return ok

    res = W(0, (0,) * m)
    return res, len(memo), len(viol)


def load_template(name_or_path):
    path = name_or_path
    if not os.path.exists(path):
        path = os.path.join(SEED_DIR, name_or_path + ".json")
    return json.load(open(path, encoding="utf-8"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", choices=["fkt", "braun_r1", "braun", "rudin"])
    ap.add_argument("--template", type=str, default=None, help="模板 JSON 路径")
    ap.add_argument("--eps", type=float, default=None, help="覆盖 rudin 模板的 eps")
    ap.add_argument("--order", choices=["fwd", "rev"], default=None, help="覆盖层序")
    ap.add_argument("--jobs", type=str, default=None)
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--check", type=str, default=None, help="阈值模式：数值")
    a = ap.parse_args()

    t0 = time.time()
    if a.jobs:
        sizes = [Fraction(int(x)) for x in a.jobs.split(",")]
        label = "custom"
        m = a.m
    else:
        name = a.template or a.seed
        if name is None:
            ap.error("need --seed / --template / --jobs")
        if name == "braun":
            name = "braun_r1"
        tpl = load_template(name)
        if a.eps is not None:
            for p in tpl.get("params", []):
                if p["name"] == "eps":
                    p["value"] = a.eps
        if a.order is not None:
            tpl["order"] = a.order
        sizes, meta = template_schema.materialize(tpl)
        label = meta["name"] + (f" [eps={a.eps}]" if a.eps is not None else "")
        m = meta["m"]

    if a.check:
        tau = Fraction(a.check).limit_denominator(10 ** 12)
        res, states, nv = check_sequence(sizes, tau, m)
        dt = time.time() - t0
        print(f"模板: {label}")
        print(f"作业数: {len(sizes)}, tau = {float(tau):.9f}")
        print(f"CHECK {'PASS' if res else 'FAIL'}: 值 >= tau {'成立' if res else '不成立'}")
        print(f"状态数: {states}, 违规状态: {nv}, 耗时 {dt:.1f}s")
    else:
        val, states = eval_sequence(sizes, m)
        dt = time.time() - t0
        print(f"模板: {label}")
        print(f"作业数: {len(sizes)}")
        print(f"值 = {float(val):.9f}  ({val})")
        print(f"状态数: {states}, 耗时 {dt:.1f}s")


if __name__ == "__main__":
    main()
