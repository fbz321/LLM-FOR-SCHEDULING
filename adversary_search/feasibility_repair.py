#!/usr/bin/env python3
"""数值可行性修复（DE 版）：对 L2 失败（负尺寸等）的模板，用微分演化在参数空间
寻找全尺寸为正的可行点。

动机（EXP-2026-08-17-A/B）：LLM 修复与纯随机搜索（1000 点，0/15）都失败——
可行域是薄流形，需要种群式连续优化。目标函数 = −min(作业尺寸)，
materialize(check_positive=False) 提供连续信号。

用法：
  python feasibility_repair.py --dir llm_pool
"""

import argparse
import datetime
import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema
import template_eval


def collect_l2_failures(dirpath):
    out = []
    for fn in sorted(os.listdir(dirpath)):
        if not fn.endswith(".json") or fn.startswith("raw_") or "_fr" in fn:
            continue
        path = os.path.join(dirpath, fn)
        try:
            tpl = json.load(open(path, encoding="utf-8"))
        except Exception:
            continue
        tpl.pop("_validation_errors", None)
        if template_schema.validate(tpl):
            continue
        try:
            template_schema.materialize(tpl)
        except template_schema.TplError as e:
            out.append((fn, tpl, str(e)))
        except Exception as e:
            out.append((fn, tpl, f"展开异常: {e}"))
    return out


def param_ranges(tpl):
    names, bounds, center = [], [], []
    for p in tpl.get("params", []):
        v = float(p.get("value", 0.5))
        b = p.get("bounds")
        if b and len(b) == 2:
            a_, b_ = float(b[0]), float(b[1])
        elif v > 0:
            a_, b_ = v / 4, v * 4
        else:
            a_, b_ = 0.01, 2.0
        if b_ <= a_:
            b_ = a_ + 0.1
        names.append(p["name"])
        bounds.append((a_, b_))
        center.append(min(max(v, a_), b_))
    return names, bounds, center


def min_job_size(tpl, names, theta):
    t2 = json.loads(json.dumps(tpl))
    for p, nm, x in zip(t2.get("params", []), names, theta):
        p["value"] = float(x)
    try:
        sizes, meta = template_schema.materialize(t2, check_positive=False)
    except Exception:
        return None, None, None
    mn = min(float(s) for s in sizes)
    return mn, sizes, meta


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--popsize", type=int, default=15)
    ap.add_argument("--maxiter", type=int, default=80)
    ap.add_argument("--workers", type=int, default=1)
    a = ap.parse_args()

    try:
        from scipy.optimize import differential_evolution
    except ImportError:
        print("需要 scipy: pip install scipy")
        sys.exit(1)

    fails = collect_l2_failures(a.dir)
    print(f"L2 失败模板 {len(fails)} 个，DE popsize={a.popsize} maxiter={a.maxiter}\n")

    rows = []
    for fn, tpl, err in fails:
        names, bounds, center = param_ranges(tpl)
        nm_tpl = tpl.get("name", "?")
        if not names:
            rows.append((fn, nm_tpl, "无自由参数", None, 0.0))
            print(f"[   SKIP] {fn} [{nm_tpl}]: 无自由参数")
            continue
        t0 = time.time()

        def obj(theta):
            mn, _, _ = min_job_size(tpl, names, theta)
            return 1e6 if mn is None else -mn

        res = differential_evolution(
            obj, bounds, popsize=a.popsize, maxiter=a.maxiter,
            workers=a.workers, updating="deferred", tol=1e-8,
            seed=0, polish=True, x0=center)
        dt = time.time() - t0
        mn, sizes, meta = min_job_size(tpl, names, res.x)
        if mn is None or mn <= 0:
            rows.append((fn, nm_tpl, f"FEAS-FAIL（最优 min_size="
                         f"{'None' if mn is None else round(mn, 6)}）", None, dt))
            print(f"[FEAS-FAIL] {fn} [{nm_tpl}]  {dt:.1f}s")
            continue

        pt = {nm: float(x) for nm, x in zip(names, res.x)}
        tau_c, tau_f = Fraction("1.70"), Fraction("1.7320")
        try:
            ok_c, _, _ = template_eval.check_sequence(sizes, tau_c, meta["m"])
            if not ok_c:
                stage = "REJECTED"
            else:
                ok_f, _, _ = template_eval.check_sequence(sizes, tau_f, meta["m"])
                stage = "CANDIDATE" if ok_f else "KNOWN-BAND"
        except Exception as e:
            stage = f"EVAL-ERR({e})"

        t2 = json.loads(json.dumps(tpl))
        for p, nm in zip(t2.get("params", []), names):
            p["value"] = pt[nm]
        t2["name"] = nm_tpl + "_fr"
        t2["description"] = (str(tpl.get("description", "")) +
                             f"【DE 数值可行性修复：{ {k: round(v, 6) for k, v in pt.items()} }】")
        out_fn = fn.replace(".json", "_fr.json")
        open(os.path.join(a.dir, out_fn), "w", encoding="utf-8").write(
            json.dumps(t2, ensure_ascii=False, indent=2))
        rows.append((fn, nm_tpl, stage, out_fn, dt))
        print(f"[{stage:>11}] {fn} [{nm_tpl}] -> {out_fn}  {dt:.1f}s  "
              f"params={ {k: round(v, 4) for k, v in pt.items()} }")

    md = ["# 数值可行性修复结果（DE）", "",
          f"目录: {a.dir}, popsize={a.popsize}, maxiter={a.maxiter}", "",
          "| 原文件 | 模板 | 结果 | 修复文件 | 耗时 |", "|---|---|---|---|---|"]
    for fn, nm, stage, out_fn, dt in rows:
        md.append(f"| {fn} | {nm} | {stage} | {out_fn or '-'} | {dt:.1f}s |")
    open(os.path.join(a.dir, "feasibility_results.md"), "w",
         encoding="utf-8").write("\n".join(md) + "\n")
    n_feas = sum(1 for r in rows if r[3])
    print(f"\n可行 {n_feas}/{len(rows)}，结果存 {a.dir}/feasibility_results.md")


if __name__ == "__main__":
    main()
