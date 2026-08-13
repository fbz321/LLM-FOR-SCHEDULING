#!/usr/bin/env python3
"""Run bottleneck reflection with DeepSeek API."""
import os, sys

from orchestrator import BottleneckOrchestrator
from llm_client import LLMClient

api_key = os.environ.get("DEEPSEEK_API_KEY", "")
if not api_key:
    print("Set DEEPSEEK_API_KEY")
    sys.exit(1)

llm = LLMClient(
    provider="deepseek",
    model="deepseek-v4-pro",
    api_key=api_key,
    max_tokens=8192,
    temperature=0.3,
)

orch = BottleneckOrchestrator(
    llm_client=llm,
    initial_rho=1.88,   # Start from Rudin's known lower bound
    delta=0.01,         # Try to push from 1.88 → 1.89 → ...
    max_iterations=10,
    max_fix_attempts=3,
    max_stuck=3,
    run_name="e2_push_1_89",
)

print("=" * 60)
print("E1: DeepSeek + Bottleneck Reflection Loop")
print("=" * 60)
final_rho = orch.run()
print(f"\nFINAL: ρ = {final_rho}")
print(f"Gap: [{final_rho}, 1.9201]")
