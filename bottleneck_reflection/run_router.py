#!/usr/bin/env python3
"""自适应模型路由入口：flash(deepseek-chat) 先试，验证失败升级 pro(deepseek-reasoner)。

用法：
    python run_router.py                                   # 用默认参数跑
    python run_router.py --target 1.89 --max-iterations 20 # 自定义
    python run_router.py --flash-model deepseek-chat --pro-model deepseek-reasoner

API key 读取顺序：
    1) 环境变量 DEEPSEEK_API_KEY
    2) 项目根目录 .env 文件（支持 `DEEPSEEK_API_KEY=...` 或裸 `sk-...` 一行）

后台运行（Linux）：
    nohup python3 -u run_router.py > /tmp/router.log 2>&1 &
    tail -f /tmp/router.log
"""
import argparse
import os
import sys

# Windows 控制台默认 GBK，打印 emoji（⚠️/✅/🧭 等）会 UnicodeEncodeError，这里强制 UTF-8。
for _stream in (sys.stdout, sys.stderr):
    if _stream is not None and hasattr(_stream, "reconfigure"):
        try:
            _stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

from orchestrator import BottleneckOrchestrator
from llm_client import LLMClient
from model_router import ModelRouter

# run_router.py 位于 <项目根>/OnlineScheduling/bottleneck_reflection/，往上三级是项目根。
PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _load_api_key() -> str:
    """环境变量优先，其次读项目根 .env。"""
    key = os.environ.get("DEEPSEEK_API_KEY", "").strip()
    if key:
        return key

    env_path = os.path.join(PROJECT_ROOT, ".env")
    if not os.path.exists(env_path):
        return ""

    with open(env_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if "=" in line:
                k, _, v = line.partition("=")
                if k.strip() == "DEEPSEEK_API_KEY" and v.strip():
                    return v.strip()
            elif line.startswith("sk-"):
                return line  # 当前 .env 就是这种裸 key 行
    return ""


def main() -> None:
    p = argparse.ArgumentParser(
        description="自适应模型路由：flash 先试，Lean 验证失败后升级 pro 重做。"
    )
    p.add_argument("--target", type=float, default=1.89,
                   help="目标竞争比（默认 1.89）")
    p.add_argument("--initial-rho", type=float, default=1.88,
                   help="起始 ρ（默认 1.88）")
    p.add_argument("--delta", type=float, default=0.01,
                   help="初始步长（默认 0.01）")
    p.add_argument("--max-iterations", type=int, default=10,
                   help="最大迭代轮数（默认 10）")
    p.add_argument("--max-fix-attempts", type=int, default=3,
                   help="每个瓶颈的修复次数（默认 3）")
    p.add_argument("--max-stuck", type=int, default=3,
                   help="触发策略重想的卡住次数（默认 3）")
    p.add_argument("--flash-model", type=str, default="deepseek-chat",
                   help="flash（便宜）模型（默认 deepseek-chat）")
    p.add_argument("--pro-model", type=str, default="deepseek-reasoner",
                   help="pro（强推理）模型（默认 deepseek-reasoner）")
    p.add_argument("--temperature", type=float, default=0.3,
                   help="采样温度（默认 0.3；reasoner 会自动忽略）")
    p.add_argument("--run-name", type=str, default="router_flash_to_pro",
                   help="本轮实验名，决定输出目录（默认 router_flash_to_pro）")
    args = p.parse_args()

    api_key = _load_api_key()
    if not api_key:
        print("未找到 API key：请设置环境变量 DEEPSEEK_API_KEY，或在项目根 .env 里放 key。")
        sys.exit(1)

    flash = LLMClient(provider="deepseek", model=args.flash_model,
                      api_key=api_key, max_tokens=4096, temperature=args.temperature)
    pro = LLMClient(provider="deepseek", model=args.pro_model,
                    api_key=api_key, max_tokens=8192, temperature=args.temperature)
    router = ModelRouter(flash, pro)

    print("=" * 62)
    print(f"  Adaptive router: {args.flash_model} (flash) → {args.pro_model} (pro)")
    print(f"  Target ρ = {args.target} | start ρ = {args.initial_rho}")
    print(f"  Max iterations = {args.max_iterations} | fixes = {args.max_fix_attempts}")
    print(f"  Run name = {args.run_name}")
    print("=" * 62)

    orch = BottleneckOrchestrator(
        router=router,
        initial_rho=args.initial_rho,
        delta=args.delta,
        max_iterations=args.max_iterations,
        max_fix_attempts=args.max_fix_attempts,
        max_stuck=args.max_stuck,
        run_name=args.run_name,
    )

    final_rho = orch.run()
    print(f"\nFINAL: ρ = {final_rho}")
    print(f"Router stats: {orch.router.stats}")
    print(f"Outputs: {orch.round_dir}")


if __name__ == "__main__":
    main()
