"""Extract structured bottlenecks from Lean compilation failures."""

from dataclasses import dataclass, field

from lean_verifier import LeanResult, get_error_category


@dataclass
class Bottleneck:
    """Structured bottleneck from a failed Lean compilation."""
    error_category: str
    goals: list[str] = field(default_factory=list)
    hypotheses: list[str] = field(default_factory=list)
    error_summary: str = ""
    nl_description: str = ""
    suggested_fix: str = ""
    location: str = ""

    def to_dict(self) -> dict:
        return {
            "error_category": self.error_category,
            "goals": self.goals,
            "hypotheses": self.hypotheses,
            "nl_description": self.nl_description,
            "suggested_fix": self.suggested_fix,
        }


def extract_bottleneck(result: LeanResult, code: str = "") -> Bottleneck:
    """
    Parse a LeanResult (failed compilation) into a structured Bottleneck.
    Produces natural language descriptions and fix suggestions.
    """
    category = get_error_category(result)

    # Get first error location
    location = ""
    if result.errors:
        e = result.errors[0]
        location = f"{e.file}:{e.line}:{e.col}" if e.file else ""

    goals = result.parsed_goals
    hyps = result.parsed_hyps

    if category == "unsolved_goals":
        return _handle_unsolved_goals(goals, hyps, result)
    elif category == "type_mismatch":
        return _handle_type_mismatch(result)
    elif category == "unknown_identifier":
        return _handle_unknown_identifier(result)
    elif category.startswith("tactic_failure"):
        return _handle_tactic_failure(category, goals, hyps, result)
    elif category == "syntax_error":
        return _handle_syntax_error(result)
    elif category == "timeout":
        return _handle_timeout(result)
    elif category == "heartbeat_limit":
        return _handle_heartbeat(result)
    else:
        return _handle_unknown(result)


def _handle_unsolved_goals(goals, hyps, result) -> Bottleneck:
    b = Bottleneck(error_category="unsolved_goals", goals=goals, hypotheses=hyps)

    if goals:
        goal_text = goals[0]
        b.nl_description = f"The proof fails to close the goal: ⊢ {goal_text}"

        if any(op in goal_text for op in ["≥", "≤", "<", ">", ">=", "<="]):
            b.nl_description += "\nThis is an inequality goal."
            if "OPT" in goal_text:
                b.nl_description += (
                    "\nIt involves OPT, which is opaque — you must bound it using "
                    "opt_le_of_schedule, opt_ge_max_job, or opt_ge_avg_load."
                )
            b.suggested_fix = (
                "Use nlinarith with the available hypotheses. If nlinarith fails, "
                "check that all hypotheses are inequalities. You may need field_simp "
                "to clear denominators first, then nlinarith."
            )
        elif "=" in goal_text:
            b.nl_description += "\nThis is an equality goal."
            if "OPT" in goal_text:
                b.nl_description += (
                    "\nIt involves computing OPT for a concrete instance. "
                    "Use opt_of_identical_jobs if all jobs are identical, "
                    "or prove both ≤ and ≥ directions with opt_le_of_schedule and opt_ge_*."
                )
            b.suggested_fix = (
                "Use calc with known identities, or apply le_antisymm to prove both directions."
            )
        elif "∃" in goal_text:
            b.nl_description += "\nThis is an existence goal."
            b.suggested_fix = (
                "Provide an explicit witness (a concrete JobSequence), then prove "
                "the remaining inequality property about that witness."
            )
        else:
            b.suggested_fix = (
                "Review what tactic was used and whether it was appropriate for this goal shape. "
                "Consider breaking the goal into smaller intermediate lemmas."
            )
    else:
        b.nl_description = "A goal could not be closed, but the specific goal could not be parsed."
        b.suggested_fix = "Check the error location in the code for the unclosed goal."

    # Add hypothesis context
    if hyps:
        b.nl_description += f"\nAvailable hypotheses: {', '.join(hyps[:8])}"

    b.error_summary = result.raw_output[:500]
    return b


def _handle_type_mismatch(result) -> Bottleneck:
    b = Bottleneck(error_category="type_mismatch")
    b.nl_description = "A type mismatch error occurred."
    b.suggested_fix = (
        "Check the type of the expression. Common fixes: use (x : ℝ) to coerce "
        "ℕ to ℝ, use Nat.cast for explicit casts, or use field_simp to handle "
        "rational arithmetic. Remember that OPT returns ℝ and m is ℕ."
    )

    # Try to extract expected/actual types
    output = result.raw_output
    if "expected" in output.lower():
        b.nl_description += "\n" + _extract_lines_containing(output, ["expected", "has type"], 3)
    b.error_summary = result.raw_output[:500]
    return b


def _handle_unknown_identifier(result) -> Bottleneck:
    b = Bottleneck(error_category="unknown_identifier")
    b.nl_description = "An unknown identifier was used."

    # Find the unknown name
    for line in result.raw_output.split("\n"):
        if "unknown identifier" in line.lower() or "unknown constant" in line.lower():
            b.nl_description += f" The error mentions: {line.strip()}"
            break

    b.suggested_fix = (
        "Check for typos in the identifier name. Ensure the lemma/theorem is imported. "
        "If it's a user-defined lemma, verify it was defined before use. "
        "All available lemmas from OnlineScheduling are listed in the system prompt."
    )
    b.error_summary = result.raw_output[:500]
    return b


def _handle_tactic_failure(category, goals, hyps, result) -> Bottleneck:
    b = Bottleneck(error_category=category, goals=goals, hypotheses=hyps)

    tactic = category.replace("tactic_failure_", "")
    b.nl_description = f"The {tactic} tactic failed to prove the goal."

    if "nlinarith" in category:
        b.nl_description += (
            "\nThis means the inequality cannot be proved from available hypotheses "
            "using linear/nonlinear arithmetic alone. The inequality may be FALSE "
            "with current values, or it may require additional algebraic manipulation."
        )
        b.suggested_fix = (
            "The job sizes may not satisfy the inequality. Try: "
            "1. Different job size values that make the algebra work. "
            "2. Adding an intermediate lemma to bound OPT differently. "
            "3. Using field_simp to clear denominators before nlinarith. "
            "4. Breaking the inequality into smaller steps with have statements."
        )
    elif "field_simp" in category:
        b.suggested_fix = (
            "field_simp may be failing because a denominator is zero. Add hypotheses "
            "that all denominators are nonzero. For example: have hpos : 0 < (m : ℝ) := "
            "by exact_mod_cast Nat.pos_of_neZero."
        )

    if goals:
        b.nl_description += f"\nGoal: ⊢ {goals[0]}"
    b.error_summary = result.raw_output[:500]
    return b


def _handle_syntax_error(result) -> Bottleneck:
    b = Bottleneck(error_category="syntax_error")
    b.nl_description = "A syntax error occurred in the Lean code."
    b.suggested_fix = (
        "Check for common syntax issues: missing 'by' after ':=' in theorem/lemma, "
        "incorrect indentation in tactic blocks, missing ';' between commands, "
        "unclosed parentheses or brackets. Ensure all 'set' commands use ':=' not ':='."
    )
    b.error_summary = result.raw_output[:500]
    return b


def _handle_timeout(result) -> Bottleneck:
    b = Bottleneck(error_category="timeout")
    b.nl_description = "Lean compilation timed out. The proof may contain an infinite loop or be too complex."
    b.suggested_fix = (
        "Simplify the proof. Break large calc blocks into separate have statements. "
        "Avoid heavy computations on large structures. If using nlinarith on many "
        "variables, try reducing the number of variables first."
    )
    b.error_summary = "Compilation timed out"
    return b


def _handle_heartbeat(result) -> Bottleneck:
    b = Bottleneck(error_category="heartbeat_limit")
    b.nl_description = "The Lean heartbeat limit was exceeded."
    b.suggested_fix = (
        "Add 'set_option maxHeartbeats 400000' at the top of the file. "
        "If still failing, simplify the proof structure."
    )
    b.error_summary = result.raw_output[:500]
    return b


def _handle_unknown(result) -> Bottleneck:
    b = Bottleneck(error_category="unknown")
    b.nl_description = "An unrecognized Lean error occurred."
    b.suggested_fix = "Review the full error output for clues. Consider simplifying the approach."
    b.error_summary = result.raw_output[:800]
    return b


def _extract_lines_containing(text: str, keywords: list[str], max_lines: int = 3) -> str:
    """Extract lines containing any of the given keywords."""
    lines = text.split("\n")
    found = []
    for line in lines:
        if any(k in line.lower() for k in [kw.lower() for kw in keywords]):
            found.append(line.strip())
            if len(found) >= max_lines:
                break
    return "\n".join(found)


if __name__ == "__main__":
    # Quick smoke test
    from lean_verifier import check_lean_code

    bad_code = '''import OnlineScheduling.Basic
open OnlineScheduling

example : 1 + 1 = 3 := by
  nlinarith
'''
    result = check_lean_code(bad_code)
    print(f"Compiles: {result.compiles}")
    b = extract_bottleneck(result, bad_code)
    print(f"Category: {b.error_category}")
    print(f"NL: {b.nl_description}")
