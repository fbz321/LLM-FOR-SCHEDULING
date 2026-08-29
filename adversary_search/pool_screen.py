#!/usr/bin/env python3
"""模板池粗筛管线（C0 漏斗）。

对一个目录里的所有模板 JSON 依次过漏斗：
  L1  schema 校验（template_schema.validate）          —— 秒级，拦格式错误
  L2  展开（materialize：解方程/递推/尺寸合法性）       —— 秒级，拦结构错误
  L3  check(tau_coarse)，默认 1.70                     —— 秒~分级，拦低值模板
  L4  check(tau_fine)，默认 1.7320（≈√3，留 slack）    —— 分级，分已知带/候选
  L5  （--exact）对候选做精确求值

分级语义：
  < coarse            REJECTED       （结构无力）
  [coarse, fine)      KNOWN-BAND     （FKT~√3 已知构造区间）
  >= fine             CANDIDATE      （√3 及以上，值得 DE 精修 + 独立验证）

LLM 生成器接口（后续接入）：把 LLM 产出的 JSON 文件放进 --dir 目录即可，
本脚本不关心模板是人写的还是模型写的。

用法：
  python pool_screen.py --dir variants
  python pool_screen.py --dir variants --coarse 1.70 --fine 1.7319 --exact
"""

import argparse
import glob
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema
import template_eval


def screen_one(path, tau_coarse, tau_fine, do_exact):
    name = os.path.basename(path)
    rec = {"file": name, "template": None, "n_jobs": None,
           "stage": None, "detail": "", "states": None, "time_s": 0.0}
    t0 = time.time()
    try:
        tpl = json.load(open(path, encoding="utf-8"))
    except Exception as e:
        rec.update(stage="L0-JSON-ERROR", detail=str(e)[:120])
        return rec
    rec["template"] = tpl.get("name", name)

    errs = template_schema.validate(tpl)                       # L1
    if errs:
        rec.update(stage="L1-INVALID", detail="; ".join(errs)[:160])
        rec["time_s"] = time.time() - t0
        return rec

    try:                                                        # L2
        sizes, meta = template_schema.materialize(tpl)
    except template_schema.TplError as e:
        rec.update(stage="L2-MATERIALIZE-FAIL", detail=str(e)[:160])
        rec["time_s"] = time.time() - t0
        return rec
    rec["n_jobs"] = meta["n_jobs"]

    try:                                                        # L3
        ok, states, nv = template_eval.check_sequence(sizes, tau_coarse, meta["m"])
    except Exception as e:
        rec.update(stage="L3-EVAL-ERROR", detail=str(e)[:120])
        rec["time_s"] = time.time() - t0
        return rec
    rec["states"] = states
    if not ok:
        rec.update(stage="REJECTED", detail=f"< {float(tau_coarse):.4f}（{states} 状态）")
        rec["time_s"] = time.time() - t0
        return rec

    try:                                                        # L4
        ok2, states2, nv2 = template_eval.check_sequence(sizes, tau_fine, meta["m"])
    except Exception as e:
        rec.update(stage="L4-EVAL-ERROR", detail=str(e)[:120])
        rec["time_s"] = time.time() - t0
        return rec
    rec["states"] = states2
    if not ok2:
        rec.update(stage="KNOWN-BAND",
                   detail=f">= {float(tau_coarse):.4f}, < {float(tau_fine):.4f}（{states2} 状态）")
        rec["time_s"] = time.time() - t0
        return rec

    rec.update(stage="CANDIDATE", detail=f">= {float(tau_fine):.4f}（{states2} 状态）")
    if do_exact:                                                # L5
        val, st = template_eval.eval_sequence(sizes, meta["m"])
        rec["detail"] += f"；精确值 = {float(val):.9f}"
        rec["states"] = st
    rec["time_s"] = time.time() - t0
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--coarse", type=str, default="1.70")
    ap.add_argument("--fine", type=str, default="1.7320")
    ap.add_argument("--exact", action="store_true")
    ap.add_argument("--skip", type=str, default="", help="逗号分隔：跳过深层模板名（单独跑）")
    ap.add_argument("--out", type=str, default=None, help="结果 markdown 输出路径")
    a = ap.parse_args()

    tau_c = template_eval.Fraction(a.coarse).limit_denominator(10 ** 12)
    tau_f = template_eval.Fraction(a.fine).limit_denominator(10 ** 12)
    skip = set(a.skip.split(",")) if a.skip else set()

    files = sorted(glob.glob(os.path.join(a.dir, "*.json")))
    recs = []
    for f in files:
        base = os.path.splitext(os.path.basename(f))[0]
        if base in skip:
            continue
        rec = screen_one(f, tau_c, tau_f, a.exact)
        recs.append(rec)
        print(f"[{rec['stage']:>22}] {rec['file']:<24} jobs={rec['n_jobs']}  "
              f"{rec['time_s']:.1f}s  {rec['detail'][:80]}")

    # 汇总
    md = ["# 模板池粗筛结果", "",
          f"漏斗阈值：coarse={a.coarse}, fine={a.fine}", "",
          "| 状态 | 模板 | 文件 | 作业数 | 状态数 | 耗时 | 详情 |",
          "|---|---|---|---|---|---|---|"]
    for r in recs:
        md.append(f"| {r['stage']} | {r['template']} | {r['file']} | "
                  f"{r['n_jobs']} | {r['states']} | {r['time_s']:.1f}s | {r['detail']} |")
    txt = "\n".join(md) + "\n"
    out = a.out or os.path.join(a.dir, "pool_results.md")
    open(out, "w", encoding="utf-8").write(txt)
    print(f"\n结果已写入 {out}")
    n_cand = sum(1 for r in recs if r["stage"] == "CANDIDATE")
    n_band = sum(1 for r in recs if r["stage"] == "KNOWN-BAND")
    print(f"CANDIDATE: {n_cand}, KNOWN-BAND: {n_band}, 其余 {len(recs) - n_cand - n_band}")


if __name__ == "__main__":
    main()
