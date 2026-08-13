"""Bottleneck Reflection Orchestrator — main loop for closing the competitive ratio gap.

Based on the Gilbert-Pollak paper's methodology (Ke et al., ICML 2026):
  Evaluate → Reflect → Propose → Translate

Usage:
  # Rediscovery experiment (E0: FKT 1.707)
  python orchestrator.py --target 1.707 --max-iterations 20

  # Push beyond known bounds
  python orchestrator.py --target 1.89 --max-iterations 50
"""

import argparse
import sys
import time
from datetime import datetime

from state_manager import StateManager, SystemState, IterationState
from lean_verifier import check_lean_code
from bottleneck_extractor import extract_bottleneck
from prompt_builder import (
    system_prompt,
    initial_proposal,
    bottleneck_fix,
    strategy_rethink,
    construct_user_message,
)
from llm_client import LLMClient, MockLLMClient


class BottleneckOrchestrator:
    """Main orchestrator for the bottleneck reflection loop."""

    def __init__(
        self,
        llm_client: LLMClient | MockLLMClient,
        initial_rho: float = 1.88,
        delta: float = 0.01,
        direction: str = "lower",
        max_iterations: int = 50,
        max_fix_attempts: int = 3,
        max_stuck: int = 5,
        run_name: str = "",
    ):
        self.llm = llm_client
        self.state = SystemState(
            rho=initial_rho,
            delta=delta,
            direction=direction,
            max_iterations=max_iterations,
            max_fix_attempts=max_fix_attempts,
            max_stuck=max_stuck,
        )
        self.state_manager = StateManager("experiments")
        self.round_dir = self.state_manager.new_round_dir(run_name)
        self._system_msg = system_prompt()
        self._total_attempts = 0

        print(f"Bottleneck Orchestrator initialized")
        print(f"  Initial ρ: {initial_rho}")
        print(f"  Delta: {delta}")
        print(f"  Direction: {direction}")
        print(f"  Max iterations: {max_iterations}")
        print(f"  Max fix attempts: {max_fix_attempts}")
        print(f"  Round dir: {self.round_dir}")

    def run(self) -> float:
        """Run the full bottleneck reflection loop. Returns final ρ."""
        print(f"\n{'='*70}")
        print(f"  BOTTLENECK REFLECTION LOOP START")
        print(f"{'='*70}")

        while (self.state.rho < 1.95 and  # Reasonable upper bound for lower bound
               self.state.iteration < self.state.max_iterations):

            target = self.state.rho + self.state.delta
            target = round(target, 6)  # Avoid floating glitches

            print(f"\n{'─'*50}")
            print(f"  ITERATION {self.state.iteration}: target ρ = {target}")
            print(f"  Current ρ = {self.state.rho}, delta = {self.state.delta}")
            print(f"{'─'*50}")

            self.state.iteration += 1

            # ── Phase 1: Propose ──
            print(f"  [PHASE 1] Proposing...")
            proposal = self._propose_initial(target)

            # ── Phase 2: Verify ──
            print(f"  [PHASE 2] Verifying with Lean...")
            success, result, code = self._verify(proposal)

            if success:
                self._handle_success(target, code, "initial proposal")
                continue

            # ── Phase 3-4: Reflect → Propose (targeted fix) ──
            print(f"  [PHASE 3] Bottleneck reflection...")
            current_code = code
            fixed = False

            for fix_attempt in range(self.state.max_fix_attempts):
                print(f"    Fix attempt {fix_attempt + 1}/{self.state.max_fix_attempts}")

                bottleneck = extract_bottleneck(result, current_code)
                print(f"    Bottleneck: {bottleneck.error_category}")
                if bottleneck.nl_description:
                    print(f"    {bottleneck.nl_description[:200]}")

                fix_prompt = bottleneck_fix(
                    target=target,
                    previous_code=current_code,
                    error_category=bottleneck.error_category,
                    goals=bottleneck.goals,
                    hypotheses=bottleneck.hypotheses,
                    nl_description=bottleneck.nl_description,
                    suggested_fix=bottleneck.suggested_fix,
                    remaining_attempts=self.state.max_fix_attempts - fix_attempt - 1,
                )
                messages = construct_user_message(self._system_msg, fix_prompt)
                fix_code = self.llm.generate(messages)
                self._total_attempts += 1

                # Save attempt
                self.state_manager.save_attempt(
                    self.round_dir, self._total_attempts, fix_code,
                    {"iteration": self.state.iteration, "target": target,
                     "fix_attempt": fix_attempt, "error_category": bottleneck.error_category}
                )

                print(f"  [PHASE 4] Re-verifying with Lean...")
                t0 = time.time()
                result2 = check_lean_code(fix_code)
                t1 = time.time()

                if result2.compiles:
                    self._handle_success(target, fix_code, f"bottleneck fix (attempt {fix_attempt + 1})")
                    fixed = True
                    break
                else:
                    print(f"    Still fails ({getattr(result2, 'error_count', '?')} errors)")
                    result = result2
                    current_code = fix_code
                    self.state.record_failure(
                        bottleneck.error_category,
                        bottleneck.nl_description
                    )

            if fixed:
                continue

            # ── All fixes failed ──
            self.state.stuck_count += 1
            self.state.record_failure(
                "all_fixes_failed",
                f"Failed to prove ρ = {target} after {self.state.max_fix_attempts} fix attempts"
            )
            print(f"  All {self.state.max_fix_attempts} fix attempts failed.")
            print(f"  Stuck count: {self.state.stuck_count}/{self.state.max_stuck}")

            if self.state.stuck_count >= self.state.max_stuck:
                print(f"  [!] Triggering STRATEGY RETHINK...")
                rethink_prompt = strategy_rethink(
                    target=target,
                    failure_summary=self.state.get_failure_summary_str(),
                    current_sizes="unknown",
                    k=self.state.stuck_count,
                )
                messages = construct_user_message(self._system_msg, rethink_prompt)
                new_approach = self.llm.generate(messages)
                self._total_attempts += 1
                self.state.last_proposal = new_approach
                self.state.stuck_count = 0
                self.state.reset_failures()
                self.state_manager.save_attempt(
                    self.round_dir, self._total_attempts, new_approach,
                    {"type": "strategy_rethink", "iteration": self.state.iteration}
                )
                print(f"  New strategy generated ({len(new_approach)} chars)")
            else:
                self.state.delta = round(self.state.delta * 0.5, 6)
                print(f"  Reducing delta to {self.state.delta}")

            # Save state
            self._save_state()

        # ── Final ──
        self._save_state()
        print(f"\n{'='*70}")
        print(f"  BOTTLENECK REFLECTION LOOP COMPLETE")
        print(f"  Final ρ: {self.state.rho}")
        print(f"  Total iterations: {self.state.iteration}")
        print(f"  Total LLM calls: {self._total_attempts}")
        print(f"  Gap remaining: [{self.state.rho}, 1.9201]")
        print(f"{'='*70}")
        return self.state.rho

    def _propose_initial(self, target: float) -> str:
        """Phase 1: Generate initial adversary proposal for target ratio."""
        if self.state.last_proposal and self.state.stuck_count == 0:
            # Reuse strategy rethink result
            return self.state.last_proposal

        prompt_text = initial_proposal(
            target=target,
            current_best=self.state.rho,
        )
        messages = construct_user_message(self._system_msg, prompt_text)
        return self.llm.generate(messages)

    def _verify(self, code: str) -> tuple[bool, object, str]:
        """Phase 2: Run Lean compilation check."""
        self._total_attempts += 1
        t0 = time.time()
        result = check_lean_code(code)
        t1 = time.time()
        elapsed = round(t1 - t0, 2)

        if result.compiles:
            print(f"    ✅ Compiles ({elapsed}s)")
        else:
            print(f"    ❌ {result.error_count} errors ({elapsed}s)")
            if result.errors:
                first = result.errors[0]
                print(f"       {first.file}:{first.line}:{first.col}: {first.message[:120]}")

        # Save attempt
        error_info = {
            "compiles": result.compiles,
            "error_count": result.error_count,
            "elapsed": elapsed,
        }
        if result.errors:
            error_info["first_error"] = result.errors[0].message[:300]
        self.state_manager.save_attempt(
            self.round_dir, self._total_attempts, code, error_info
        )

        return result.compiles, result, code

    def _handle_success(self, target: float, code: str, source: str):
        """Handle a successful proof."""
        print(f"    🎉 SUCCESS! Proved lower bound ρ ≥ {target} (via {source})")
        old_rho = self.state.rho
        self.state.rho = target
        self.state.delta = round(self.state.delta * 1.5, 6)
        self.state.delta = min(self.state.delta, 0.05)  # Cap delta
        self.state.stuck_count = 0
        self.state.reset_failures()
        self.state.best_proof = code

        self.state_manager.save_proof(self.round_dir, target, code)

        self.state.save_history(IterationState(
            iteration=self.state.iteration,
            target=target,
            rho_before=old_rho,
            result="success",
            code=code[:500],
        ))
        self._save_state()

    def _save_state(self):
        """Persist current state."""
        self.state_manager.save(self.state, self.round_dir)


def main():
    parser = argparse.ArgumentParser(
        description="Bottleneck Reflection for P|online,list|Cmax competitive ratio gap"
    )
    parser.add_argument("--target", type=float, default=1.89,
                        help="Target competitive ratio (default: 1.89)")
    parser.add_argument("--initial-rho", type=float, default=1.88,
                        help="Starting ρ (default: 1.88)")
    parser.add_argument("--delta", type=float, default=0.01,
                        help="Initial step size (default: 0.01)")
    parser.add_argument("--max-iterations", type=int, default=50,
                        help="Max iterations (default: 50)")
    parser.add_argument("--max-fix-attempts", type=int, default=3,
                        help="Max fix attempts per bottleneck (default: 3)")
    parser.add_argument("--max-stuck", type=int, default=5,
                        help="Max stuck iterations before rethink (default: 5)")
    parser.add_argument("--model", type=str, default="sonnet",
                        help="LLM model (default: sonnet)")
    parser.add_argument("--provider", type=str, default="claude",
                        help="LLM provider (default: claude)")
    parser.add_argument("--mock", action="store_true",
                        help="Use mock LLM client (no API calls)")
    parser.add_argument("--run-name", type=str, default="",
                        help="Name for this experiment run")
    parser.add_argument("--temperature", type=float, default=0.3,
                        help="LLM temperature (default: 0.3)")
    args = parser.parse_args()

    # Create LLM client
    if args.mock:
        llm = MockLLMClient()
        print("⚠️  Using MOCK LLM client — no API calls will be made")
    else:
        llm = LLMClient(
            provider=args.provider,
            model=args.model,
            temperature=args.temperature,
        )

    # Create and run orchestrator
    orch = BottleneckOrchestrator(
        llm_client=llm,
        initial_rho=args.initial_rho,
        delta=args.delta,
        max_iterations=args.max_iterations,
        max_fix_attempts=args.max_fix_attempts,
        max_stuck=args.max_stuck,
        run_name=args.run_name,
    )

    final_rho = orch.run()

    print(f"\n{'='*70}")
    print(f"  FINAL RESULT: ρ ≥ {final_rho}")
    print(f"  Gap: [{final_rho}, 1.9201]")
    print(f"  All outputs in: {orch.round_dir}")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
