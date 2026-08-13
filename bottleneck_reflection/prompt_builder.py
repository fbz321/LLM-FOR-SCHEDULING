"""Build prompts for the bottleneck reflection system."""

import os
from typing import Optional

PROMPTS_DIR = os.path.join(os.path.dirname(__file__), "prompts")


def _load_prompt(name: str) -> str:
    path = os.path.join(PROMPTS_DIR, name)
    if not os.path.exists(path):
        return f"[MISSING PROMPT: {name}]"
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def system_prompt() -> str:
    return _load_prompt("system.txt")


def initial_proposal(target: float, current_best: float = 1.88) -> str:
    """Build the initial adversary proposal prompt."""
    template = _load_prompt("initial_proposal.txt")
    delta = round(target - current_best, 4)
    return template.format(
        target=target,
        current_best=current_best,
        delta=delta,
    )


def bottleneck_fix(
    target: float,
    previous_code: str,
    error_category: str,
    goals: list[str],
    hypotheses: list[str],
    nl_description: str,
    suggested_fix: str,
    remaining_attempts: int = 2,
) -> str:
    """Build the bottleneck-targeted fix prompt."""
    template = _load_prompt("bottleneck_fix.txt")

    goals_section = ""
    if goals:
        goals_section = "FAILED GOALS:\n" + "\n".join(f"  ⊢ {g}" for g in goals)
    else:
        goals_section = "(No specific goals could be extracted from error output)"

    hypotheses_section = ""
    if hypotheses:
        hypotheses_section = "AVAILABLE HYPOTHESES:\n" + "\n".join(f"  {h}" for h in hypotheses[:12])

    # Generate specific guidance based on error category
    guidance = _specific_guidance(error_category, goals)

    return template.format(
        target=target,
        error_category=error_category,
        goals_section=goals_section,
        hypotheses_section=hypotheses_section,
        nl_description=nl_description,
        suggested_fix=suggested_fix,
        guidance=guidance,
        remaining_attempts=remaining_attempts,
        previous_code=previous_code[:8000],  # Truncate if very long
    )


def strategy_rethink(
    target: float,
    failure_summary: str,
    current_sizes: str = "unknown",
    k: int = 5,
) -> str:
    """Build the strategy rethink prompt."""
    template = _load_prompt("strategy_rethink.txt")
    return template.format(
        target=target,
        k=k,
        failure_summary=failure_summary,
        current_sizes=current_sizes,
    )


def construct_user_message(
    system: str,
    specific_prompt: str,
    message_history: Optional[list[dict]] = None,
) -> list[dict]:
    """Build a complete messages list for the LLM API."""
    messages = [{"role": "system", "content": system}]

    if message_history:
        messages.extend(message_history)

    messages.append({"role": "user", "content": specific_prompt})
    return messages


def _specific_guidance(error_category: str, goals: list[str]) -> str:
    """Generate extra-specific guidance based on error pattern."""
    goal_text = goals[0] if goals else ""

    if error_category == "unsolved_goals":
        if "OPT" in goal_text and ("≥" in goal_text or "≤" in goal_text):
            return (
                "The goal involves an inequality with OPT. Since OPT is opaque, "
                "you need to bound it. For lower bound: use opt_ge_max_job or "
                "opt_ge_avg_load to get OPT ≥ something. For upper bound: use "
                "opt_le_of_schedule with a concrete uniform schedule — assign each "
                "of the m machines exactly (totalLoad/m) load. Then prove "
                "totalLoad = m * (totalLoad/m) using field_simp."
            )
        if "∃" in goal_text:
            return (
                "You need to provide an explicit sigma (JobSequence). "
                "Use `use σ₂` (or whatever your sequence variable is) to provide "
                "the witness, then prove the inequality for that sigma."
            )

    if error_category == "type_mismatch":
        return (
            "Type mismatch between ℕ and ℝ is the most common issue. "
            "Use `(m : ℝ)` to cast m to ℝ. "
            "Use `exact_mod_cast` to convert inequalities from ℕ to ℝ. "
            "Use `have hm_rat : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm`."
        )

    if error_category.startswith("tactic_failure"):
        return (
            "The tactic couldn't close the goal. This often means the inequality "
            "is FALSE with the chosen values. Try: (1) check if the inequality "
            "actually holds numerically for m=4 with your chosen sizes — if not, "
            "change the sizes. (2) Add field_simp to clear denominators before "
            "nlinarith. (3) Use `have` statements to calculate intermediate values."
        )

    return "Review the error message carefully and ensure the proof step is mathematically valid."
