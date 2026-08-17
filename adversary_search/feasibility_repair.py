#!/usr/bin/env python3
"""数值可行性修复：对 L2 失败（负尺寸等）的模板，在参数空间随机搜索可行点。

动机（EXP-2026-08-17-A 结论）：LLM 修复循环两轮都救不活 Rudin/Braun 族负尺寸，
因为失败是数值问题（参数越出可行域）而非结构问题——交给数值方法。

策略：
  - 参数搜索域：模板声明的 bounds；否则 [value/4, value*4]（value<=0 时 [0.01, 2]）
  - 随机采样 N 次（默认 800）：materialize 成功（全部尺寸为正）= 可行点
  - 可行模板再过漏斗 check(1.70)/check(1.7320)
  - 产出 <原名>_fr.json（参数替换为可行值）

用法：
  python feasibility_repair.py --dir llm_pool_r2
  python feasibility_repair.py --dir llm_pool --samples 2000
"""

import argparse
import datetime
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema
import template_eval
from fractions import Fraction


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
    names, lo, hi, center = [], [], [], []
    for p in tpl.get("params", []):
        v = float(p.get("value", 0.5))
        b = p.get("bounds")
        if b and len(b) == 2:
            a_, b_ = float(b[0]), float(b[1])
        elif v > 0:
            a_, b_ = v / 4, v * 4
        else:
            a_, b_ = 0.01, 2.0
        names.append(p["name"])
        lo.append(a_)
        hi.append(b_)
        center.append(min(max(v, a_), b_))
    return names, lo, hi, center


def try_materialize(tpl, names, point):
    t2 = json.loads(json.dumps(tpl))
    for p, nm in zip(t2.get("params", []), names):
        p["value"] = point[nm]
    try:
        sizes, meta = template_schema.materialize(t2)
        return t2, sizes, meta
    except Exception:
        return None, None, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--samples", type=int, default=800)
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()

    rng = random.Random(a.seed)
    fails = collect_l2_failures(a.dir)
    print(f"L2 失败模板 {len(fails)} 个，每个随机搜索 {a.samples} 点\n")

    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    rows = []
    for fn, tpl, err in fails:
        names, lo, hi, center = param_ranges(tpl)
        if not names:
            rows.append((fn, tpl.get("name"), "无自由参数，跳过", None, None))
            continue
        t0 = time.time()
        found = None
        for s in range(a.samples):
            pt = {nm: rng.uniform(l, h) for nm, l, h in zip(names, lo, hi)}
            # 每 50 次采样插入一次中心点邻域（小幅扰动）
            if s % 50 == 0:
                pt = {nm: min(max(c + rng.uniform(-0.05, 0.05) * (h - l), l), h)
                      for nm, c, l, h in zip(names, center, lo, hi)}
            t2, sizes, meta = try_materialize(tpl, names, pt)
            if t2 is not None:
                found = (pt, t2, sizes, meta)
                break
        if found is None:
            rows.append((fn, tpl.get("name"), f"FEAS-FAIL（{a.samples} 点无可行）",
                         None, time.time() - t0))
            continue
        pt, t2, sizes, meta = found
        # 过漏斗
        tau_c = Fraction("1.70")
        tau_f = Fraction("1.7320")
        try:
            ok_c, st_c, _ = template_eval.check_sequence(sizes, tau_c, meta["m"])
            stage = "REJECTED" if not ok_c else None
            if ok_c:
                ok_f, st_f, _ = template_eval.check_sequence(sizes, tau_f, meta["m"])
                stage = "CANDIDATE" if ok_f else "KNOWN-BAND"
        except Exception as e:
            stage = f"EVAL-ERR({e})"
        t2["name"] = str(tpl.get("name", "?")) + "_fr"
        t2["description"] = (str(tpl.get("description", "")) +
                             f"【数值可行性修复：{names}={ {k: round(v, 6) for k, v in pt.items()} }】")
        out_fn = fn.replace(".json", "_fr.json")
        open(os.path.join(a.dir, out_fn), "w", encoding="utf-8").write(
            json.dumps(t2, ensure_ascii=False, indent=2))
        rows.append((fn, tpl.get("name"), stage, out_fn, time.time() - t0))
        print(f"[{stage:>11}] {fn} -> {out_fn}  ({time.time() - t0:.1f}s, "
              f"可行点 { {k: round(v, 4) for k, v in pt.items()} })")

    # 汇总
    md = ["# 数值可行性修复结果", "",
          f"目录: {a.dir}, 采样: {a.samples}, seed: {a.seed}", "",
          "| 原文件 | 模板 | 结果 | 修复文件 | 耗时 |", "|---|---|---|---|---|"]
    for fn, nm, stage, out_fn, dt in rows:
        md.append(f"| {fn} | {nm} | {stage} | {out_fn or '-'} | "
                  f"{dt:.1f}s |" if dt is not None else f"| {fn} | {nm} | {stage} | - | - |")
    open(os.path.join(a.dir, "feasibility_results.md"), "w",
         encoding="utf-8").write("\n".join(md) + "\n")
    n_feas = sum(1 for r in rows if r[3])
    print(f"\n可行 {n_feas}/{len(rows)}，结果存 {a.dir}/feasibility_results.md")


if __name__ == "__main__":
    main()
