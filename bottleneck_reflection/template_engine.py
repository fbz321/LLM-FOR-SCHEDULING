"""Fill verified Lean template with numeric parameters from LLM.

Model A (creative): Proposes job sizes → returns JSON
Template engine: Fills numeric params into pre-verified Lean skeleton
Lean verifier: Checks the filled proof compiles
"""

import re
import json
from fractions import Fraction


def render(params: dict) -> str:
    """Render the adversary template with given parameters.

    Required params:
        target: float — target competitive ratio
        a1, a2: str — job sizes as Lean ℝ expressions (e.g. "1/2", "(1:ℝ)/3")
        F: str — final job size

    Optional params:
        a3: str — third layer job size (enables 3-layer adversary)
        extra_layer: bool — whether to include a3 layer
    """
    template = _load_template()

    target = params["target"]
    a1 = params["a1"]
    a2 = params["a2"]
    F = params["F"]

    # Clean numeric strings to ensure ℝ type
    def to_real(s: str) -> str:
        s = s.strip()
        # If it's a bare rational like "1/2", wrap it
        if re.match(r'^-?\d+/\d+$', s):
            return f"({s} : ℝ)"
        # If it's a decimal, convert to rational
        if re.match(r'^-?\d+\.\d+$', s):
            f = Fraction(s)
            return f"({f.numerator} : ℝ)/{f.denominator}"
        return s

    target_real = to_real(str(target))
    target_short = str(target).replace(".", "_")
    a1_real = to_real(a1)
    a2_real = to_real(a2)
    F_real = to_real(F)

    # Layer 3 (optional)
    if params.get("a3"):
        a3 = params["a3"]
        a3_real = to_real(a3)
        a3_line = f"set a₃ := {a3_real} with ha₃_def"
        a3pos_line = "have ha₃pos : 0 < a₃ := by norm_num [ha₃_def]"
        phase3_block = f"""let τ₃ := List.replicate m a₃
      set loads₃ := τ₃.foldl (step (m := m) alg) loads₂ with h_loads₃_def
      set σ₃ := σ₂ ++ τ₃ with hσ₃_def
      have h_p3 := layer_separation_from_base (m := m) alg (a₁ + a₂) a₃ ha₃pos loads₂ h_loads2
      rcases h_p3 with (h_imbal3 | h_bal3)
      · use σ₃
        have h_sched : totalLoad σ₃ = ∑ i : Fin m, (λ _ : Fin m => a₁ + a₂ + a₃) i := by
          dsimp [σ₃, σ₂, σ₁, τ₂, τ₃, totalLoad]; simp [hσ₁_def]; ring
        have h_opt : OPT σ₃ ≤ a₁ + a₂ + a₃ :=
          opt_le_of_schedule (m := m) σ₃ (λ _ => a₁ + a₂ + a₃) h_sched
        rw [{a1_real}, {a2_real}, {a3_real}]
        norm_num
        nlinarith
      · have h_loads3 : ∀ i : Fin m, loads₃ i = a₁ + a₂ + a₃ := h_bal3
        set loads_last := loads₃ with h_loads_last_def
        set prev_sigma := σ₃ with h_prev_sigma_def"""
        final_sigma = "σ₃ ++ [F]"
        all_sigmas = "σ₃, σ₂, σ₁, τ₂, τ₃"
        opt_bound = "a₁ + a₂ + a₃ + F/(m : ℝ)"
        mk_bound = "a₁ + a₂ + a₃ + F"
        prev_sigma = "σ₃"
        rewrites = f"{a1_real}, {a2_real}, {a3_real}, hF_def"
    else:
        a3_line = ""
        a3pos_line = ""
        phase3_block = ""
        final_sigma = "σ₂ ++ [F]"
        all_sigmas = "σ₂, σ₁, τ₂"
        opt_bound = "a₁ + a₂ + F/(m : ℝ)"
        mk_bound = "a₁ + a₂ + F"
        prev_sigma = "σ₂"
        rewrites = f"{a1_real}, {a2_real}, hF_def"

    replacements = {
        "{{TARGET_SHORT}}": target_short,
        "{{TARGET}}": target_real,
        "{{A1}}": a1_real,
        "{{A2}}": a2_real,
        "{{A3_LINE}}": a3_line,
        "{{A3POS_LINE}}": a3pos_line,
        "{{F}}": F_real,
        "{{PHASE3_BLOCK}}": phase3_block,
        "{{FINAL_SIGMA}}": final_sigma,
        "{{ALL_SIGMAS}}": all_sigmas,
        "{{OPT_BOUND}}": opt_bound,
        "{{MK_BOUND}}": mk_bound,
        "{{PREV_SIGMA}}": prev_sigma,
        "{{REWRITES}}": rewrites,
    }

    result = template
    for key, val in replacements.items():
        result = result.replace(key, val)

    return result


def _load_template() -> str:
    import os
    path = os.path.join(os.path.dirname(__file__), "templates", "adversary_template.lean")
    with open(path) as f:
        return f.read()


# ── Model A: conjecture proposer ──

CONJECTURE_PROMPT = """You are an expert in online scheduling theory.
Propose job sizes for a layered adversary to achieve competitive ratio {target}.

The adversary has 2 or 3 layers of m identical jobs each, plus one final job.
Return ONLY a JSON object with these fields:
{{
  "a1": "rational like 1/2",
  "a2": "rational like 1/3",
  "a3": "rational like 1/4 or null if 2 layers only",
  "F": "rational like 1",
  "reasoning": "brief explanation of why these sizes should work"
}}

Strategy: After k layers, the sum S = a1 + a2 (+ a3).
Makespan ≥ S + F (one machine gets the final job).
OPT ≤ S + F/m (uniform schedule).
Need: (S+F) / (S + F/m) ≥ {target}.
Worst case m=4: (S+F) / (S + F/4) ≥ {target}.
Choose S and F to satisfy this inequality with margin."""


if __name__ == "__main__":
    # Quick test
    params = {"target": 1.25, "a1": "1/2", "a2": "1/2", "F": "1"}
    code = render(params)
    print(code[:500])
    print("...")
    print(f"Total: {len(code)} chars")
