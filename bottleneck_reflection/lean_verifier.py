"""Lean 4 compilation verifier with structured error parsing."""

import subprocess
import re
import uuid
import os
from dataclasses import dataclass, field
from typing import Optional

LEAN_PROJECT_PATH = os.environ.get("LEAN_PROJECT_PATH", os.path.join(os.path.dirname(__file__), ".."))

# Use absolute paths (nohup doesn't inherit PATH); override with env vars.
LAKE_BIN = os.environ.get("LAKE_BIN", "lake")
LEAN_BIN = os.environ.get("LEAN_BIN", "lean")
LAKE_CMD = [LAKE_BIN, "env", "lean"]


@dataclass
class LeanError:
    """A single parsed Lean compilation error."""
    file: str = ""
    line: int = 0
    col: int = 0
    severity: str = "error"
    message: str = ""


@dataclass
class LeanResult:
    """Result of a Lean compilation check."""
    compiles: bool
    raw_output: str
    errors: list[LeanError] = field(default_factory=list)
    error_count: int = 0
    parsed_goals: list[str] = field(default_factory=list)  # unsolved ⊢ goals
    parsed_hyps: list[str] = field(default_factory=list)   # hypotheses for first goal


_NOISE_PATTERNS = [
    "manifest out of date",
    "use `lake update",
    "warning: mathlib:",
    "has local changes",
    "Declarations whose name ends with a `_`",
]


def _filter_noise(text: str) -> str:
    lines = text.split("\n")
    return "\n".join(
        l for l in lines
        if not any(pat in l for pat in _NOISE_PATTERNS)
    ).strip()


def check_lean_code(code: str, timeout: int = 120) -> LeanResult:
    """
    Write code to a temp file in the Lean project root and run `lake env lean`.
    Returns LeanResult with compilation status and parsed errors.
    """
    unique_name = f"_br_{uuid.uuid4().hex[:8]}.lean"
    dest_path = os.path.join(LEAN_PROJECT_PATH, unique_name)

    try:
        with open(dest_path, "w", encoding="utf-8") as f:
            f.write(code)

        result = subprocess.run(
            LAKE_CMD + [unique_name],
            cwd=LEAN_PROJECT_PATH,
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        stderr = _filter_noise(result.stderr)
        stdout = _filter_noise(result.stdout)
        all_output = (stdout + "\n" + stderr).strip()

        success = result.returncode == 0 and not _has_error(all_output) and not _has_sorry(all_output)
        errors = _parse_errors(all_output) if not success else []
        goals, hyps = _parse_unsolved_goals(all_output)

        return LeanResult(
            compiles=success,
            raw_output=all_output,
            errors=errors,
            error_count=len(errors),
            parsed_goals=goals,
            parsed_hyps=hyps,
        )

    except subprocess.TimeoutExpired:
        return LeanResult(
            compiles=False,
            raw_output="Compilation timed out",
            errors=[LeanError(message="Lean compilation timed out")],
            error_count=1,
        )
    except FileNotFoundError:
        return LeanResult(
            compiles=False,
            raw_output=f"Lean binary not found at {LEAN_BIN}",
            errors=[LeanError(message=f"Lean binary not found at {LEAN_BIN}")],
            error_count=1,
        )
    finally:
        try:
            if os.path.exists(dest_path):
                os.unlink(dest_path)
        except (OSError, FileNotFoundError):
            pass


def _has_error(output: str) -> bool:
    """Check if output contains actual Lean errors (not just warnings)."""
    for line in output.split("\n"):
        stripped = line.strip()
        if ": error:" in stripped or stripped.startswith("error:"):
            return True
    return False


def _has_sorry(output: str) -> bool:
    """Check if output contains 'sorry' warning — code compiles but proof is incomplete."""
    return "uses `sorry`" in output or "declaration uses 'sorry'" in output


def _parse_errors(output: str) -> list[LeanError]:
    """Parse structured Lean errors from compiler output."""
    errors = []
    pattern = r"([^\s:]+\.lean):(\d+):(\d+):\s*(error|warning):\s*(.*?)(?=\n[^\s:]+\.lean:\d+:\d+:\s*(?:error|warning):|\Z)"
    for match in re.finditer(pattern, output, re.DOTALL):
        errors.append(LeanError(
            file=match.group(1),
            line=int(match.group(2)),
            col=int(match.group(3)),
            severity=match.group(4),
            message=match.group(5).strip(),
        ))

    # Catch standalone "unsolved goals" blocks not captured by the above
    if not errors and ("unsolved goals" in output.lower() or "error:" in output.lower()):
        errors.append(LeanError(message=output.strip()))

    return errors


def _parse_unsolved_goals(output: str) -> tuple[list[str], list[str]]:
    """Extract ⊢ goals and hypotheses from unsolved_goals errors."""
    goals = []
    hyps = []

    # Find ⊢ lines
    for line in output.split("\n"):
        stripped = line.strip()
        if stripped.startswith("⊢"):
            goals.append(stripped[1:].strip())

    # Find hypotheses for the first goal
    # Look for blocks like "m : ℕ\nhm : 4 ≤ m\nalg : OnlineAlgorithm m" before ⊢
    lines = output.split("\n")
    in_goal_block = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("⊢"):
            break
        if "error:" in stripped.lower() and "unsolved goals" in stripped.lower():
            in_goal_block = True
            continue
        if in_goal_block:
            # A hypothesis looks like "name : type" or "name : type := value"
            if ":" in stripped and not stripped.startswith("⊢") and not stripped.startswith("---"):
                hyps.append(stripped)

    return goals, hyps


def get_error_category(result: LeanResult) -> str:
    """Classify the primary error into a category for bottleneck extraction."""
    full = (result.raw_output.lower() + " " +
            " ".join(e.message.lower() for e in result.errors))

    # Check for sorry first
    if "uses `sorry`" in full or "declaration uses 'sorry'" in full:
        return "unsolved_goals"

    # Order matters — check more specific patterns first
    if "unsolved goals" in full:
        return "unsolved_goals"
    if "type mismatch" in full or "has type" in full:
        return "type_mismatch"
    if "unknown identifier" in full or "unknown constant" in full:
        return "unknown_identifier"
    if "nlinarith" in full and ("fail" in full or "error" in full):
        return "tactic_failure_nlinarith"
    if "linarith" in full and ("fail" in full or "error" in full):
        return "tactic_failure_linarith"
    if "field_simp" in full and ("fail" in full or "error" in full):
        return "tactic_failure_field_simp"
    if "failed to find a contradiction" in full:
        return "tactic_failure_linarith"
    if "syntax" in full or "unexpected token" in full:
        return "syntax_error"
    if "timed out" in full or "timeout" in full:
        return "timeout"
    if "simp made no progress" in full:
        return "tactic_failure_simp"
    if "omega" in full and ("fail" in full or "error" in full):
        return "tactic_failure_omega"
    if "don't know how to synthesize placeholder" in full:
        return "unsolved_goals"
    if "tactic" in full and ("fail" in full or "error" in full):
        return "tactic_failure"
    if "heartbeat" in full.lower():
        return "heartbeat_limit"

    return "unknown"


if __name__ == "__main__":
    # Quick smoke test
    code = '''import OnlineScheduling.Basic
open OnlineScheduling

example : 1 + 1 = 2 := by
  norm_num
'''
    r = check_lean_code(code)
    print(f"Compiles: {r.compiles}, errors: {r.error_count}")
