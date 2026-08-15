#!/usr/bin/env python3
"""Braun 2025 补完入口：flash→pro 自适应路由驱动 BraunGraham2025.lean 剩余引理。

用法：
    python braun_router.py
    python braun_router.py --max-fix-attempts 3 --run-name braun_v1

逻辑：按 SUBGOALS 顺序，每个子目标先让 flash 生成证明 → 插入 BraunGraham2025.lean
副本单文件编译验证；失败自动升级 pro 重做；仍失败则进入瓶颈修复循环。成功一个就
提交进工作副本，供后续子目标引用。
"""
import argparse
import os
import sys

for _s in (sys.stdout, sys.stderr):
    if hasattr(_s, "reconfigure"):
        try:
            _s.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

from llm_client import LLMClient
from model_router import ModelRouter
from braun_verifier import BraunVerifier
from run_router import _load_api_key

HERE = os.path.dirname(os.path.abspath(__file__))

# 剩余子目标（按序）。statement 是完整声明（不含 `by` 证明），LLM 输出完整声明 + 证明。
# 2026-08-15：全部子目标已完成并提交进 BraunGraham2025.lean（0 sorry，已入湖
# OnlineScheduling.LowerBounds.BraunGraham2025）：
#   - braun_opt_prefix_Sp（Table 6 前缀 OPT = S⁺_k + L_k）
#   - braun_asymptotic_lower_bound（Theorem 1 主定理，r=1 自适应对抗）
# 列表保留为空；若将来启动一般 r 强制归纳（Theorem 2/全参数族），在此登记新子目标。
SUBGOALS = []


def _load(path: str) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def _system() -> str:
    return _load(os.path.join(HERE, "prompts", "braun_system.txt"))


def _task_messages(statement: str, hint: str) -> list:
    tmpl = _load(os.path.join(HERE, "prompts", "braun_task.txt"))
    context = f"提示：{hint}" if hint else ""
    user = tmpl.format(statement=statement, context=context)
    return [{"role": "system", "content": _system()}, {"role": "user", "content": user}]


def _fix_messages(prev_code: str, error: str) -> list:
    user = (
        f"上一个方案 Lean 编译失败，错误如下：\n{error[:1500]}\n\n"
        f"失败代码：\n```lean\n{prev_code}\n```\n\n"
        "请修正后重新只输出完整 Lean 声明（不要 import/open/namespace/end）。"
    )
    return [{"role": "system", "content": _system()}, {"role": "user", "content": user}]


def _error_summary(result) -> str:
    errors = getattr(result, "errors", None) or []
    if errors:
        msg = getattr(errors[0], "message", "") or str(errors[0])
        return msg[:1500]
    return (getattr(result, "raw_output", "") or "").strip()[:1500]


def main() -> None:
    p = argparse.ArgumentParser(description="flash→pro 路由驱动 BraunGraham2025.lean 补完")
    p.add_argument("--flash-model", type=str, default="deepseek-chat")
    p.add_argument("--pro-model", type=str, default="deepseek-reasoner")
    p.add_argument("--temperature", type=float, default=0.3)
    p.add_argument("--max-fix-attempts", type=int, default=3)
    p.add_argument("--run-name", type=str, default="braun_router")
    p.add_argument("--no-api", action="store_true", help="只跑冒烟，不调 LLM")
    args = p.parse_args()

    verifier = BraunVerifier()

    out_dir = os.path.join(HERE, "experiments", args.run_name)
    os.makedirs(out_dir, exist_ok=True)

    if args.no_api:
        print("Dry-run: 冒烟验证 braun_opt_prefix_Sp 声明能否被插入（不调 LLM）")
        r = verifier.verify("theorem braun_opt_prefix_Sp (k : ℕ) (hk : 1 ≤ k) :\n"
                            "    optMakespan (m := 4) (braunPrefixSp k) = braunSp k + braunL k := by\n"
                            "  sorry")
        print(f"  (带 sorry 应被判定 compiles=False) compiles={r.compiles}, errors={r.error_count}")
        return

    api_key = _load_api_key()
    if not api_key:
        print("未找到 API key：设置环境变量 DEEPSEEK_API_KEY 或在项目根 .env 放 key。")
        sys.exit(1)

    flash = LLMClient(provider="deepseek", model=args.flash_model,
                      api_key=api_key, max_tokens=8192, temperature=args.temperature)
    pro = LLMClient(provider="deepseek", model=args.pro_model,
                    api_key=api_key, max_tokens=16384, temperature=args.temperature)
    router = ModelRouter(flash, pro)

    print("=" * 64)
    print(f"  Braun 2025 补完路由: {args.flash_model} (flash) → {args.pro_model} (pro)")
    print(f"  子目标数: {len(SUBGOALS)} | 修复次数上限: {args.max_fix_attempts}")
    print(f"  输出目录: {out_dir}")
    print("=" * 64)

    for idx, goal in enumerate(SUBGOALS, 1):
        print(f"\n[SUBGOAL {idx}/{len(SUBGOALS)}] {goal['name']}")
        messages = _task_messages(goal["statement"], goal.get("hint", ""))
        rr = router.generate_and_verify("initial_proposal", messages, verifier.verify)
        cur_code = rr.code
        cur_result = rr.result

        if cur_result.compiles:
            verifier.commit(cur_code)
            print(f"  ✅ 编译通过（{rr.model_used}），已提交。")
            continue

        print(f"  ❌ 初次失败（{rr.model_used}，{cur_result.error_count} errors），进入修复循环。")

        fixed = False
        for attempt in range(args.max_fix_attempts):
            print(f"    fix {attempt + 1}/{args.max_fix_attempts} ...")
            fm = _fix_messages(cur_code, _error_summary(cur_result))
            fr = router.generate_and_verify("bottleneck_fix", fm, verifier.verify)
            if fr.result.compiles:
                verifier.commit(fr.code)
                print(f"    ✅ 修复成功（{fr.model_used}），已提交。")
                fixed = True
                break
            cur_code = fr.code
            cur_result = fr.result
            print(f"    ❌ 仍失败（{fr.model_used}，{cur_result.error_count} errors）")

        if not fixed:
            print(f"  ⚠️ 子目标 {goal['name']} 未解决，跳到下一个。")

    # 汇总
    print("\n" + "=" * 64)
    print(f"  成功提交 {len(verifier.committed)} / {len(SUBGOALS)} 个子目标")
    print("=" * 64)

    merged_path = os.path.join(out_dir, "BraunGraham2025.merged.lean")
    with open(merged_path, "w", encoding="utf-8") as f:
        f.write(verifier.current_src)
    frags_path = os.path.join(out_dir, "fragments.txt")
    with open(frags_path, "w", encoding="utf-8") as f:
        f.write("\n\n----\n\n".join(verifier.committed))

    print(f"  合并结果: {merged_path}")
    print(f"  成功片段: {frags_path}")
    print(f"  Router stats: {router.stats}")


if __name__ == "__main__":
    main()
