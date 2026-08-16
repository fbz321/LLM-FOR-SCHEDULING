#!/usr/bin/env python3
"""模板约束求值器（A3'/C0 步骤 1-3）。

与 m4_search 的自由 minimax 不同：这里对抗者的作业序列由模板完全固定
（层结构 + 尺寸），只有调度器分支。

精确模式  值 = min_调度器 max_前缀 makespan/OPT（真下界语义）。
阈值模式  --check tau：只验证 值 >= tau（对抗者早停剪枝，快几个量级），
          并输出违规状态集 = 强制证书（C1 GameTree 叶子的雏形）。

OPT_i 只依赖前缀索引 i，预计算一次。种子结构提取自已证 Lean 形式化：
  FKT   <- Faigle.lean；Braun <- BraunGraham2025Abs.lean；Rudin <- Rudin.lean

用法：
  python template_eval.py --seed fkt
  python template_eval.py --seed braun --check 1.731
  python template_eval.py --seed rudin --eps 0.0001 --order rev [--check auto]
  python template_eval.py --jobs 207,207,207,207,500,500,500,500,1000
"""

import argparse
import math
import os
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m4_search import opt  # 精确 OPT（分支定界枚举，lru_cache）

getcontext().prec = 60
DENOM_CAP = 10 ** 20


def dec2frac(x):
    return Fraction(x).limit_denominator(DENOM_CAP)


def sqrt3_dec():
    return Decimal(3).sqrt()


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
    """阈值模式：验证 值 >= tau（Fraction）。
    W(i, loads) := ratio_i >= tau 或 对所有不同负载放置 W(i+1, ...)。
    返回 (通过?, 状态数, 违规状态数)。"""
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


# ---------------------------------------------------------------- seeds
def seed_fkt():
    a, b, c = Fraction(207, 1000), Fraction(1, 2), Fraction(1)
    return [a] * 4 + [b] * 4 + [c]


def seed_braun():
    """Braun2025 Thm2 r=1：c1 = 6c^3-28c^2+38c-13 在 [5/3,2] 的根。
    序列 L0x4, S0x4, L1x4, S1x3, Sp1, F（17 作业）。"""
    f = lambda c: 6 * c ** 3 - 28 * c ** 2 + 38 * c - 13
    fp = lambda c: 18 * c ** 2 - 56 * c + 38
    c = Decimal("1.73")
    for _ in range(200):
        c -= f(c) / fp(c)
    c = dec2frac(c)
    S0 = (c - 1) / (2 - c)
    L1 = Fraction(3) / (3 * c - 5) - (c - 1) / (2 - c)
    S1 = Fraction(6) / (3 * c - 5) + (3 - c) / (2 - c)
    Sp1 = S1 + 2 * S0
    F = 2 * S1
    return [Fraction(1)] * 4 + [S0] * 4 + [L1] * 4 + [S1] * 3 + [Sp1, F], c


def seed_rudin(eps, order="rev"):
    """Rudin 2003 m=4（Rudin.lean：rudinStep/rudinLayerJobs）。
    默认 rev = 论文顺序（层 n 在前）——实测 fwd 顺序值仅 5/3。"""
    eps_d = Decimal(str(eps))
    V_d = sqrt3_dec() - 1 - eps_d
    M_d = (3 * V_d - 2) / 2
    V, M = dec2frac(V_d), dec2frac(M_d)

    S, A, B = Fraction(1), 1 / (2 * V), 1 - 1 / (2 * V) - M * (1 / (2 * V))
    layers = [(S, A, B)]
    n = None
    for i in range(1, 60):
        S2, A2 = M * A, (A - 2 * B) / 4
        R2 = A2 / S2
        B2 = S2 - A2 if R2 >= V else S2 - A2 - M * A2
        S, A, B = S2, A2, B2
        layers.append((S, A, B))
        if R2 >= V:
            n = i
            break
    assert n is not None, "60 层内未终止"
    for i, (s_, a_, b_) in enumerate(layers):
        assert b_ > 0, f"层 {i} 的 B 非正（eps 落在坏窗口）: B={float(b_):.3e}"

    jobs = []
    idx = range(n, -1, -1) if order == "rev" else range(n + 1)
    for i in idx:
        Si, Ai, Bi = layers[i]
        big = Ai if i == n else Ai + 2 * layers[i + 1][1]
        jobs += [Bi] * 4 + [Ai] * 3 + [big]
    jobs.append(2 * layers[0][1])
    return jobs, n, V


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", choices=["fkt", "braun", "rudin"])
    ap.add_argument("--eps", type=float, default=0.01)
    ap.add_argument("--order", choices=["fwd", "rev"], default="rev")
    ap.add_argument("--jobs", type=str, default=None)
    ap.add_argument("--m", type=int, default=4)
    ap.add_argument("--check", type=str, default=None,
                    help="阈值模式：'auto'（种子自带 tau）或数值")
    a = ap.parse_args()

    t0 = time.time()
    tau_auto = None
    if a.jobs:
        sizes = [Fraction(int(x)) for x in a.jobs.split(",")]
        label = "custom"
    elif a.seed == "fkt":
        sizes = seed_fkt()
        label = "FKT (4x0.207, 4x0.5, 1)"
        tau_auto = Fraction(1707, 1000)
    elif a.seed == "braun":
        sizes, c = seed_braun()
        label = f"Braun r=1 (c1~{float(c):.6f})"
        tau_auto = c
    elif a.seed == "rudin":
        sizes, n, V = seed_rudin(a.eps, a.order)
        label = f"Rudin eps={a.eps} order={a.order} n={n} (1+V={float(1 + V):.6f})"
        tau_auto = 1 + V
    else:
        ap.error("need --seed or --jobs")

    if a.check:
        tau = tau_auto if a.check == "auto" else Fraction(a.check).limit_denominator(10 ** 12)
        res, states, nv = check_sequence(sizes, tau, a.m)
        dt = time.time() - t0
        print(f"种子: {label}")
        print(f"作业数: {len(sizes)}, tau = {float(tau):.9f}")
        print(f"CHECK {'PASS' if res else 'FAIL'}: 值 >= tau {'成立' if res else '不成立'}")
        print(f"状态数: {states}, 违规状态: {nv}, 耗时 {dt:.1f}s")
    else:
        val, states = eval_sequence(sizes, a.m)
        dt = time.time() - t0
        print(f"种子: {label}")
        print(f"作业数: {len(sizes)}")
        print(f"值 = {float(val):.9f}  ({val})")
        print(f"状态数: {states}, 耗时 {dt:.1f}s")


if __name__ == "__main__":
    main()
