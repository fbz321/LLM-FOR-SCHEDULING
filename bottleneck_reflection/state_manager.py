"""Iteration state persistence for bottleneck reflection."""

import json
import os
import time
from dataclasses import dataclass, field, asdict
from typing import Optional
from datetime import datetime


@dataclass
class IterationState:
    """Immutable snapshot of one iteration's result."""
    iteration: int
    target: float
    rho_before: float
    result: str  # "success" | "bottleneck_fixed" | "all_failed" | "strategy_rethink"
    code: str = ""
    error_category: str = ""
    nl_description: str = ""
    llm_tokens: int = 0
    lean_compile_time: float = 0.0
    timestamp: str = ""

    def __post_init__(self):
        if not self.timestamp:
            self.timestamp = datetime.now().isoformat()


@dataclass
class SystemState:
    """Full state of the bottleneck reflection system."""
    rho: float = 1.88           # Current best ρ
    delta: float = 0.01         # Step size
    direction: str = "lower"    # "lower" (improve lower bound) or "upper"
    iteration: int = 0
    stuck_count: int = 0
    max_stuck: int = 5
    max_fix_attempts: int = 3
    max_iterations: int = 50
    history: list[dict] = field(default_factory=list)
    best_proof: str = ""
    last_proposal: str = ""
    failure_summary: list[str] = field(default_factory=list)

    def save_history(self, state: IterationState):
        """Append an iteration result to history."""
        self.history.append(asdict(state))

    def record_failure(self, error_category: str, nl: str):
        """Record a failure for summary."""
        self.failure_summary.append(f"[{error_category}] {nl[:200]}")

    def reset_failures(self):
        self.failure_summary = []

    def get_failure_summary_str(self) -> str:
        recent = self.failure_summary[-10:]  # Last 10
        if not recent:
            return "No failure details recorded."
        return "\n\n".join(f"  {i+1}. {f}" for i, f in enumerate(recent))


class StateManager:
    """Persist and load system state from disk."""

    def __init__(self, experiments_dir: str):
        # If relative, resolve relative to this file's directory
        if not os.path.isabs(experiments_dir):
            base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            experiments_dir = os.path.join(base, experiments_dir)
        self.experiments_dir = experiments_dir
        os.makedirs(experiments_dir, exist_ok=True)

    def save(self, state: SystemState, round_dir: str):
        """Save full state to a round directory."""
        os.makedirs(round_dir, exist_ok=True)
        path = os.path.join(round_dir, "state.json")
        data = {
            "rho": state.rho,
            "delta": state.delta,
            "direction": state.direction,
            "iteration": state.iteration,
            "stuck_count": state.stuck_count,
            "history": state.history,
            "last_updated": datetime.now().isoformat(),
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)

    def load(self, round_dir: str) -> Optional[SystemState]:
        """Load state from a round directory."""
        path = os.path.join(round_dir, "state.json")
        if not os.path.exists(path):
            return None
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        state = SystemState(
            rho=data.get("rho", 1.88),
            delta=data.get("delta", 0.01),
            iteration=data.get("iteration", 0),
            stuck_count=data.get("stuck_count", 0),
        )
        state.history = data.get("history", [])
        return state

    def save_proof(self, round_dir: str, target: float, code: str):
        """Save a successful proof."""
        os.makedirs(round_dir, exist_ok=True)
        path = os.path.join(round_dir, f"proof_rho_{str(target).replace('.', '_')}.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)

    def save_attempt(self, round_dir: str, attempt_num: int, code: str, result: dict):
        """Save a failed attempt for debugging."""
        os.makedirs(round_dir, exist_ok=True)
        path = os.path.join(round_dir, f"attempt_{attempt_num:03d}.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)
        result_path = os.path.join(round_dir, f"attempt_{attempt_num:03d}.json")
        with open(result_path, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2, ensure_ascii=False)

    def new_round_dir(self, run_name: str = "") -> str:
        """Create a new round directory."""
        ts = time.strftime("%Y%m%d_%H%M%S")
        name = run_name or f"round_{ts}"
        path = os.path.join(self.experiments_dir, name)
        os.makedirs(path, exist_ok=True)
        return path
