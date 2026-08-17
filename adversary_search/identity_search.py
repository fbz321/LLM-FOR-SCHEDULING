#!/usr/bin/env python3
"""EXP-D：魔法常数自动发现闭环（优化 -> 猜代数 -> 精确验证）。

族：几何层塔（终作业 = 1 固定，缩放不变性）
  层 k = 0..L-1：4 个尺寸 s0*t^k 的作业；终作业 1。
  FKT = L=2 特例（理论最优 t = 1+sqrt(2)，s0 = 1-sqrt(2)/2，值 1+sqrt(2)/2）。

闭环：
  1) DE 优化 (s0, t) 最大化精确 minimax 值
  2) 猜代数：候选常数库匹配（小二次无理数 (a+b*sqrt(D))/c）优先，
     mpmath PSLQ 兜底
  3) 精确验证：猜出的极小多项式 -> 60 位牛顿根 -> 重建模板 -> 精确复评，
     复评值 >= DE 值 - 1e-9 即确认恒等式

用法：
  python identity_search.py                  # L=2,3
  python identity_search.py --L 2 --maxiter 60
"""

import argparse
import math
import os
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_eval

DENOM_CAP = 10 ** 20


def dec2frac(x):
    return Fraction(x).limit_denominator(DENOM_CAP)


def build_geo_jobs(s0, t, L):
    jobs = []
    sz = Decimal(s0)
    tt = Decimal(t)
    for _ in range(L):
        jobs.extend([dec2frac(sz)] * 4)
        sz = sz * tt
    jobs.append(Fraction(1))
    return jobs


def eval_value(s0, t, L):
    jobs = build_geo_jobs(s0, t, L)
    val, states = template_eval.eval_sequence(jobs, 4)
    return float(val), val, states


def optimize(L, popsize, maxiter):
    from scipy.optimize import differential_evolution

    def obj(x):
        try:
            v, _, _ = eval_value(x[0], x[1], L)
        except Exception:
            return 1e6
        return -v

    bounds = [(0.03, 0.6), (1.05, 5.0)]
    res = differential_evolution(obj, bounds, popsize=popsize, maxiter=maxiter,
                                 workers=1, updating="deferred", tol=1e-12,
                                 seed=0, polish=True)
    v, val_frac, states = eval_value(res.x[0], res.x[1], L)
    return res.x[0], res.x[1], v, val_frac, states


def library_guess(x, tol=3e-3):
    """候选常数库：(a + b*sqrt(D))/c 的小二次无理数 + 有理数。
    返回 (误差, 候选值, 极小多项式系数[低次->高次], 描述)。"""
    best = None
    for D in (2, 3, 5, 6, 7):
        r = math.sqrt(D)
        for a in range(-6, 7):
            for b in range(-8, 9):
                if b == 0:
                    continue
                for c in range(1, 7):
                    cand = (a + b * r) / c
                    d = abs(cand - x)
                    if d < tol * max(1.0, abs(x)):
                        # 极小多项式 (c z - a)^2 - b^2 D = c^2 z^2 - 2ac z + a^2 - b^2 D
                        rel = [a * a - b * b * D, -2 * a * c, c * c]
                        desc = f"({a}+{b}*sqrt({D}))/{c}"
                        if best is None or d < best[0]:
                            best = (d, cand, rel, desc)
    if best is not None:
        return best
    # 有理数兜底：要求极高精度（避免抢走二次无理数的匹配）
    fr = Fraction(str(round(x, 12))).limit_denominator(500)
    if abs(float(fr) - x) < 1e-8:
        return (abs(float(fr) - x), float(fr),
                [-fr.numerator, fr.denominator], f"{fr}")
    return None


def pslq_guess(x, degree=4, prec=50):
    import mpmath
    mpmath.mp.dps = prec
    xf = mpmath.mpf(str(x))
    for d in range(2, degree + 1):
        vec = [xf ** k for k in range(d + 1)]
        rel = mpmath.pslq(vec, maxcoeff=10 ** 8, maxsteps=300)
        if rel is None or rel[-1] == 0:
            continue
        # 粗略根验证
        try:
            import sympy as sp
            p = sum(sp.Integer(rel[k]) * sp.Symbol("z") ** k for k in range(d + 1))
            roots = sp.nroots(p, n=15)
            err = min(abs(complex(r) - complex(float(x))) for r in roots)
            if err < 1e-6:
                return list(rel), float(err)
        except Exception:
            continue
    return None


def newton_poly(coeffs, guess, prec_digits=55):
    getcontext().prec = prec_digits + 10
    x = Decimal(str(guess))
    for _ in range(400):
        f = sum(Decimal(coeffs[k]) * x ** k for k in range(len(coeffs)))
        df = sum(Decimal(k * coeffs[k]) * x ** (k - 1)
                 for k in range(1, len(coeffs)))
        if df == 0:
            break
        xn = x - f / df
        if abs(xn - x) < Decimal(10) ** (-(prec_digits + 5)):
            x = xn
            break
        x = xn
    getcontext().prec = 60
    return x


def identify_and_verify(x, L, other_param, is_t):
    """猜 x 的代数身份并精确重建验证。is_t: x 是 t（s0=other 固定）否则 x 是 s0。"""
    g = library_guess(x)
    src = "常数库"
    if g is None:
        pg = pslq_guess(x)
        if pg is None:
            return None
        rel, err = pg
        cand = x
        desc = f"PSLQ {rel}"
        src = "PSLQ"
    else:
        err, cand, rel, desc = g
    # 精确重建：多项式的根（取 x 附近）
    xr = newton_poly(rel, x)
    if is_t:
        v2, vf2, st2 = eval_value(other_param, xr, L)
    else:
        v2, vf2, st2 = eval_value(xr, other_param, L)
    return {"source": src, "desc": desc, "poly": rel, "match_err": err,
            "rebuild_value": v2, "rebuild_frac": str(vf2), "states": st2}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=str, default="2,3")
    ap.add_argument("--popsize", type=int, default=15)
    ap.add_argument("--maxiter", type=int, default=40)
    ap.add_argument("--out", type=str,
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "identity_results.md"))
    a = ap.parse_args()

    Ls = [int(x) for x in a.L.split(",")]
    rows = []
    for L in Ls:
        t0 = time.time()
        print(f"=== L={L} DE 优化 ===", flush=True)
        s0, t, v, val_frac, states = optimize(L, a.popsize, a.maxiter)
        dt = time.time() - t0
        print(f"  数值最优: s0={s0:.9f} t={t:.9f} 值={v:.9f} states={states} "
              f"{dt:.0f}s", flush=True)

        idt = identify_and_verify(t, L, s0, is_t=True)
        ids = identify_and_verify(s0, L, t, is_t=False)
        if idt:
            print(f"  t 身份[{idt['source']}]: {idt['desc']} poly={idt['poly']} "
                  f"(匹配误差 {idt['match_err']:.2e}); 重建值={idt['rebuild_value']:.9f}",
                  flush=True)
        else:
            print("  t 无代数身份候选", flush=True)
        if ids:
            print(f"  s0 身份[{ids['source']}]: {ids['desc']} poly={ids['poly']} "
                  f"(匹配误差 {ids['match_err']:.2e}); 重建值={ids['rebuild_value']:.9f}",
                  flush=True)
        else:
            print("  s0 无代数身份候选", flush=True)
        rows.append({"L": L, "s0": s0, "t": t, "value": v, "states": states,
                     "time_s": dt, "id_t": idt, "id_s0": ids})

    # 报告
    rep = ["# EXP-D：魔法常数自动发现（几何层塔族）", "",
           f"DE popsize={a.popsize} maxiter={a.maxiter}；"
           "族：4x(s0*t^k), k=0..L-1，终作业 1", "",
           "| L | s0* | t* | 值* | t 身份 | s0 身份 | 重建值(t) | 重建值(s0) | 耗时 |",
           "|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        idt, ids = r["id_t"], r["id_s0"]
        rep.append(
            f"| {r['L']} | {r['s0']:.6f} | {r['t']:.6f} | {r['value']:.9f} | "
            f"{idt['desc'] if idt else '-'} | {ids['desc'] if ids else '-'} | "
            f"{('%.9f' % idt['rebuild_value']) if idt else '-'} | "
            f"{('%.9f' % ids['rebuild_value']) if ids else '-'} | "
            f"{r['time_s']:.0f}s |")
    rep += ["",
            "对照：FKT 理论最优 t = 1+sqrt(2) = 2.4142136，s0 = 1-sqrt(2)/2 = 0.2928932",
            "（s0 有多种等价缩放，如 0.2071 对应 b=0.5 的归一化），值 = 1+sqrt(2)/2 = 1.7071068",
            "sqrt(3) = 1.7320508；判定：重建值 >= 数值最优 - 1e-9 即恒等式确认"]
    open(a.out, "w", encoding="utf-8").write("\n".join(rep) + "\n")
    print(f"\n报告已写入 {a.out}")


if __name__ == "__main__":
    main()
