/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Braun–Chung–Graham 2025, Theorem 2: absolute competitive ratio (r = 1)

The absolute-ratio construction reuses the layer skeleton of Theorem 1 (Table 3)
but the task lengths are rational functions of the target ratio `c` (which is
strictly below √3), not the geometric series of the asymptotic analysis.

For r = 1 the layers are L₀, S₀, L₁, S₁ (plus task S⁺₁ = S₁ + 2·S₀) and the final
job F = 2·S₁. The target absolute ratio c₁ is the fixed point

    c = (L₀ + S₀ + L₁ + S₁ + F) / F,

which (Table 12) is the unique root in (5/3, 2) of `6c³ − 28c² + 38c − 13 = 0`.
-/

import Mathlib
import OnlineScheduling.Basic

namespace OnlineScheduling

noncomputable section

/-! ### Parametric task lengths (r = 1) -/

/-- S₀ = (c−1)/(2−c). -/
def braunAbsS0 (c : ℝ) : ℝ := (c - 1) / (2 - c)

/-- L₁ = 3/(3c−5) − (c−1)/(2−c). -/
def braunAbsL1 (c : ℝ) : ℝ := 3 / (3 * c - 5) - (c - 1) / (2 - c)

/-- S₁ = 6/(3c−5) + (3−c)/(2−c). -/
def braunAbsS1 (c : ℝ) : ℝ := 6 / (3 * c - 5) + (3 - c) / (2 - c)

/-- S⁺₁ = S₁ + 2·S₀. -/
def braunAbsSp1 (c : ℝ) : ℝ := braunAbsS1 c + 2 * braunAbsS0 c

/-- F = 2·S₁. -/
def braunAbsF1 (c : ℝ) : ℝ := 2 * braunAbsS1 c

/-- Σ_{i=0..1}(Lᵢ+Sᵢ) = L₀ + S₀ + L₁ + S₁, with L₀ = 1. -/
def braunAbsLayerSum1 (c : ℝ) : ℝ := 1 + braunAbsS0 c + braunAbsL1 c + braunAbsS1 c

/-- The r = 1 job sequence (17 jobs): L₀×4, S₀×4, L₁×4, S₁×3, S⁺₁, F. -/
def braunAbsSeq1 (c : ℝ) : JobSequence :=
  List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++
  List.replicate 4 (braunAbsL1 c) ++ List.replicate 3 (braunAbsS1 c) ++
  [braunAbsSp1 c] ++ [braunAbsF1 c]

/-! ### The fixed point ⟺ the cubic -/

/-- The polynomial identity: `(3c²−11c+10)·(c·F − (Σ+F)) = 6c³ − 28c² + 38c − 13`. -/
lemma braunAbs_cubic_identity (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) :
    (3 * c ^ 2 - 11 * c + 10) * (braunAbsF1 c * c - (braunAbsLayerSum1 c + braunAbsF1 c))
      = 6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 := by
  dsimp [braunAbsF1, braunAbsLayerSum1, braunAbsS0, braunAbsL1, braunAbsS1]
  field_simp [h2, h3]
  ring

/-- The fixed-point equation for r = 1 is equivalent to `6c³ − 28c² + 38c − 13 = 0`
    (paper Table 12, r = 1). -/
lemma braunAbs_cubic (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) (hF : braunAbsF1 c ≠ 0) :
    c = (braunAbsLayerSum1 c + braunAbsF1 c) / braunAbsF1 c ↔
      6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 = 0 := by
  have hD : 3 * c ^ 2 - 11 * c + 10 ≠ 0 := by
    have hfac : 3 * c ^ 2 - 11 * c + 10 = (c - 2) * (3 * c - 5) := by ring
    rw [hfac]
    exact mul_ne_zero (sub_ne_zero.mpr h2) h3
  have hid := braunAbs_cubic_identity c h2 h3
  constructor
  · intro h
    have hmul : braunAbsF1 c * c = braunAbsLayerSum1 c + braunAbsF1 c := by
      have h' := h
      field_simp [hF] at h'
      simpa [mul_comm] using h'
    have hsub : braunAbsF1 c * c - (braunAbsLayerSum1 c + braunAbsF1 c) = 0 := by
      rw [hmul]
      ring
    have hpoly : (3 * c ^ 2 - 11 * c + 10) * (braunAbsF1 c * c - (braunAbsLayerSum1 c + braunAbsF1 c)) = 0 := by
      rw [hsub, mul_zero]
    rwa [hid] at hpoly
  · intro h
    have hpoly : (3 * c ^ 2 - 11 * c + 10) * (braunAbsF1 c * c - (braunAbsLayerSum1 c + braunAbsF1 c)) = 0 := by
      rw [hid, h]
    have hsub : braunAbsF1 c * c - (braunAbsLayerSum1 c + braunAbsF1 c) = 0 :=
      (mul_eq_zero.mp hpoly).resolve_left hD
    have hmul : braunAbsF1 c * c = braunAbsLayerSum1 c + braunAbsF1 c := sub_eq_zero.mp hsub
    exact (eq_div_iff hF).mpr (by simpa [mul_comm] using hmul)

end

end OnlineScheduling
