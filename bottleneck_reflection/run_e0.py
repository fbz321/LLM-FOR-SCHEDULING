#!/usr/bin/env python3
"""E0 Experiment: DeepSeek + Lean kernel bottleneck reflection."""
import os, sys

from orchestrator import BottleneckOrchestrator
from llm_client import LLMClient

api_key = os.environ.get("DEEPSEEK_API_KEY", "")
if not api_key:
    print("Set DEEPSEEK_API_KEY")
    sys.exit(1)

llm = LLMClient(
    provider="deepseek",
    model="deepseek-chat",
    api_key=api_key,
    max_tokens=4096,
    temperature=0.3,
)

orch = BottleneckOrchestrator(
    llm_client=llm,
    initial_rho=1.0,
    delta=0.5,
    max_iterations=5,
    max_fix_attempts=2,
    max_stuck=3,
    run_name="e0_deepseek",
)

print("=" * 60)
print("E0 DEEPSEEK: Target 1.5 (below FKT 1.707)")
print("=" * 60)
final_rho = orch.run()
print(f"\nFINAL: ρ = {final_rho}")
