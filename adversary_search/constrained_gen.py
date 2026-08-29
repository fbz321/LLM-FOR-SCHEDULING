#!/usr/bin/env python3
"""受约束变异生成器（EXP-B 设计转向的落地）。

核心原则：**LLM 选配置，不写数学**。
Rudin 族的递推/代数从 seeds/rudin.json 原样继承（可行性由构造保证，
100% 可展开），只暴露经过论证的安全旋钮：

  eps         ∈ (0, 0.0099]  接近 √3 的程度（越小层数越多、值越接近 √3）
  final_mult  ∈ {1,2,3}      终作业 = final_mult × A_first（规范值 2）
  big_coeff   ∈ {1,2,3}      大作业 = A + big_coeff × A_next（规范值 2）
  order       ∈ {rev,fwd}    层序（规范值 rev）

改变 final_mult/big_coeff 会破坏 Rudin 的精确坍缩证明，但模板仍可展开，
漏斗测量真实 minimax 值——这正好检验"代数坍缩"论点：值对系数扰动是
稳健还是崩塌。

模式：
  python constrained_gen.py --grid              # 无 LLM 网格基线
  python constrained_gen.py --llm --n 12        # LLM 提议旋钮组合
  python constrained_gen.py --knobs eps=0.001,final_mult=2  # 单点
"""

import argparse
import copy
import datetime
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import template_schema

HERE = os.path.dirname(os.path.abspath(__file__))
RUDIN_SEED = os.path.join(HERE, "seeds", "rudin.json")

EPS_GRID = [0.009, 0.005, 0.001, 0.0005, 0.0001]
MULT_GRID = [1, 2, 3]
COEFF_GRID = [1, 2, 3]


def build_template(eps, final_mult, big_coeff, order="rev"):
    """从 Rudin 种子构造受约束变体。递推/代数锁死，只改三个旋钮。"""
    seed = json.load(open(RUDIN_SEED, encoding="utf-8"))
    tpl = copy.deepcopy(seed)
    # eps 旋钮
    for p in tpl["params"]:
        if p["name"] == "eps":
            p["value"] = eps
    # 层 emit：改大作业组合系数 big_coeff
    for layer in tpl["layers"]:
        for e in layer.get("emit", []):
            if e.get("size", "").startswith("where(i==n"):
                e["size"] = f"where(i==n, A, A+{big_coeff}*A_next)"
    # final 旋钮
    for e in tpl.get("final", []):
        e["size"] = f"{final_mult}*A_first"
    tpl["order"] = order
    tpl["name"] = f"cvar_rudin_eps{eps}_fm{final_mult}_bc{big_coeff}_{order}"
    tpl["description"] = (
        f"受约束变异（Rudin 族，递推锁死）：eps={eps}, final_mult={final_mult}, "
        f"big_coeff={big_coeff}, order={order}。检验值对系数扰动的稳健性。")
    tpl["base_seed"] = "rudin"
    tpl["knobs"] = {"eps": eps, "final_mult": final_mult,
                    "big_coeff": big_coeff, "order": order}
    return tpl


def instantiate_and_save(knobs_list, outdir):
    os.makedirs(outdir, exist_ok=True)
    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    written = []
    for i, k in enumerate(knobs_list):
        tpl = build_template(float(k["eps"]), int(k["final_mult"]),
                             int(k["big_coeff"]), k.get("order", "rev"))
        errs = template_schema.validate(tpl)
        if errs:
            print(f"  [INVALID] {tpl['name']}: {errs[:1]}")
            continue
        # 可展开性自检（受约束变异应 100% 通过）
        try:
            jobs, meta = template_schema.materialize(tpl)
        except template_schema.TplError as e:
            print(f"  [MAT-FAIL] {tpl['name']}: {str(e)[:80]}")
            continue
        fn = f"cvar_{ts}_{i:02d}.json"
        open(os.path.join(outdir, fn), "w", encoding="utf-8").write(
            json.dumps(tpl, ensure_ascii=False, indent=2))
        written.append(fn)
        print(f"  [OK] {fn} {tpl['name']}  jobs={meta['n_jobs']}")
    return written


def grid_knobs():
    out = []
    for eps in EPS_GRID:
        for fm in MULT_GRID:
            for bc in COEFF_GRID:
                out.append({"eps": eps, "final_mult": fm,
                            "big_coeff": bc, "order": "rev"})
    return out


LLM_SYSTEM = """你是调度理论研究员。Rudin 族对抗模板的递推代数已经锁死并验证可行，
你只需要选择"配置旋钮"，不需要写任何数学。可用旋钮：
  eps         ∈ (0, 0.0099]  越小值越接近 √3≈1.7320508，但层数/作业数越多
  final_mult  ∈ {1,2,3}      终作业系数（规范值 2）
  big_coeff   ∈ {1,2,3}      大作业 A+c*A_next 的系数（规范值 2）
  order       ∈ {"rev","fwd"} 层序（规范值 rev；fwd 已知大幅掉值）
目标：找到 minimax 值尽量高的配置（≥1.732 是 √3 级，≥1.707 合格）。
已知：规范配置(eps 小, final_mult=2, big_coeff=2, order=rev)给出 √3−eps。
你的任务是提出**有信息量的扰动假设**：哪些旋钮组合可能保持高值、哪些会崩。
只输出 JSON 数组，每个元素形如
{"eps":0.001,"final_mult":2,"big_coeff":2,"order":"rev","hypothesis":"..."}
"""


def llm_knobs(n, model):
    from generate import call_qwen
    import generate as gen
    api_key = os.environ.get("DASHSCOPE_API_KEY")
    if not api_key:
        print("错误：DASHSCOPE_API_KEY 未设置")
        sys.exit(1)
    user = f"提出 {n} 个互不相同、覆盖不同假设的旋钮组合。只输出 JSON 数组。"
    text, usage = call_qwen(api_key, model,
                            [{"role": "system", "content": LLM_SYSTEM},
                             {"role": "user", "content": user}],
                            0.9, 4000, no_think=True)
    print(f"LLM usage={usage}")
    from generate import extract_json_array
    arr = extract_json_array(text)
    knobs = []
    for item in arr:
        try:
            knobs.append({"eps": float(item["eps"]),
                          "final_mult": int(item["final_mult"]),
                          "big_coeff": int(item["big_coeff"]),
                          "order": str(item.get("order", "rev"))})
        except Exception as e:
            print(f"  [跳过非法配置] {item}: {e}")
    return knobs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", action="store_true")
    ap.add_argument("--llm", action="store_true")
    ap.add_argument("--n", type=int, default=12)
    ap.add_argument("--model", type=str, default=None)
    ap.add_argument("--knobs", type=str, default=None,
                    help="单点：eps=0.001,final_mult=2,big_coeff=2,order=rev")
    ap.add_argument("--out", type=str, default=os.path.join(HERE, "cvar_pool"))
    a = ap.parse_args()

    if a.knobs:
        k = dict(x.split("=") for x in a.knobs.split(","))
        knobs = [{"eps": k.get("eps", 0.001), "final_mult": k.get("final_mult", 2),
                  "big_coeff": k.get("big_coeff", 2), "order": k.get("order", "rev")}]
    elif a.grid:
        knobs = grid_knobs()
    elif a.llm:
        import generate as gen
        knobs = llm_knobs(a.n, a.model or gen.DEFAULT_MODEL)
    else:
        ap.error("需要 --grid / --llm / --knobs 之一")

    print(f"生成 {len(knobs)} 个受约束变体到 {a.out}")
    written = instantiate_and_save(knobs, a.out)
    print(f"\n成功实例化 {len(written)}/{len(knobs)}（受约束变异应 ~100%）")
    print("下一步：python pool_screen.py --dir " + os.path.basename(a.out))


if __name__ == "__main__":
    main()
