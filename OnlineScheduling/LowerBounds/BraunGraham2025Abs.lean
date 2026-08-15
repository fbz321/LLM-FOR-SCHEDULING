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

/-! ### The cubic root c₁ -/

/-- The cubic has a root strictly between 5/3 and 2 (intermediate value theorem). -/
lemma braunAbs_cubic_root_exists :
    ∃ c : ℝ, 5 / 3 < c ∧ c < 2 ∧ 6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 = 0 := by
  let g : ℝ → ℝ := fun c => -(6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13)
  have hcont : ContinuousOn g (Set.Icc (5 / 3 : ℝ) 2) := by
    unfold g
    fun_prop
  have h5m : (5 / 3 : ℝ) ∈ Set.Icc (5 / 3 : ℝ) 2 := by
    show (5 / 3 : ℝ) ≤ (5 / 3 : ℝ) ∧ (5 / 3 : ℝ) ≤ (2 : ℝ)
    constructor <;> norm_num
  have h2m : (2 : ℝ) ∈ Set.Icc (5 / 3 : ℝ) 2 := by
    show (5 / 3 : ℝ) ≤ (2 : ℝ) ∧ (2 : ℝ) ≤ (2 : ℝ)
    constructor <;> norm_num
  have himage := isPreconnected_Icc.intermediate_value (a := (5 / 3 : ℝ)) (b := 2) h5m h2m hcont
  have hzero : (0 : ℝ) ∈ Set.Icc (g (5 / 3 : ℝ)) (g 2) := by
    constructor <;> dsimp [g] <;> norm_num
  rcases himage hzero with ⟨c, hcmem, hceq⟩
  have hroot : 6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 = 0 := by
    dsimp [g] at hceq
    nlinarith
  have hc_lo : (5 / 3 : ℝ) < c := by
    have hne : (5 / 3 : ℝ) ≠ c := by
      intro h
      have : g (5 / 3 : ℝ) = 0 := by rw [h]; exact hceq
      dsimp [g] at this
      norm_num at this
    exact lt_of_le_of_ne hcmem.1 hne
  have hc_hi : c < 2 := by
    have hne : c ≠ 2 := by
      intro h
      have : g (2 : ℝ) = 0 := by rw [h] at hceq; exact hceq
      dsimp [g] at this
      norm_num at this
    exact lt_of_le_of_ne hcmem.2 (by simpa [eq_comm] using hne)
  exact ⟨c, hc_lo, hc_hi, hroot⟩

/-- The target absolute competitive ratio c₁ (the root in (5/3, 2)). -/
def braunAbsCR1 : ℝ := Classical.choose braunAbs_cubic_root_exists

/-- c₁ > 5/3. -/
lemma braunAbsCR1_lo : (5 / 3 : ℝ) < braunAbsCR1 := (Classical.choose_spec braunAbs_cubic_root_exists).1

/-- c₁ < 2. -/
lemma braunAbsCR1_hi : braunAbsCR1 < 2 := (Classical.choose_spec braunAbs_cubic_root_exists).2.1

/-- c₁ satisfies the cubic. -/
lemma braunAbsCR1_root :
    6 * braunAbsCR1 ^ 3 - 28 * braunAbsCR1 ^ 2 + 38 * braunAbsCR1 - 13 = 0 :=
  (Classical.choose_spec braunAbs_cubic_root_exists).2.2

/-- Side condition: c₁ ≠ 2. -/
lemma braunAbsCR1_ne_two : braunAbsCR1 ≠ 2 := by
  intro h
  nlinarith [braunAbsCR1_hi, h]

/-- Side condition: 3·c₁ − 5 ≠ 0. -/
lemma braunAbsCR1_3c5_ne : 3 * braunAbsCR1 - 5 ≠ 0 := by
  intro h
  nlinarith [braunAbsCR1_lo, h]

/-- S₁(c) > 0 on (5/3, 2). -/
lemma braunAbsS1_pos (c : ℝ) (hlo : (5 / 3 : ℝ) < c) (hhi : c < 2) : 0 < braunAbsS1 c := by
  dsimp [braunAbsS1]
  have h3 : 0 < 3 * c - 5 := by nlinarith
  have h2c : 0 < 2 - c := by nlinarith
  have h3c : 0 < 3 - c := by nlinarith
  have h1 : 0 < 6 / (3 * c - 5) := div_pos (by norm_num) h3
  have h2' : 0 < (3 - c) / (2 - c) := div_pos h3c h2c
  exact add_pos h1 h2'

/-- Side condition: F(c₁) ≠ 0. -/
lemma braunAbsF1_CR1_ne : braunAbsF1 braunAbsCR1 ≠ 0 := by
  have hpos : 0 < braunAbsF1 braunAbsCR1 := by
    dsimp [braunAbsF1]
    have hS : 0 < braunAbsS1 braunAbsCR1 := braunAbsS1_pos braunAbsCR1 braunAbsCR1_lo braunAbsCR1_hi
    nlinarith
  exact ne_of_gt hpos

/-- c₁ is the fixed point: c₁ = (Σ + F)/F. -/
lemma braunAbsCR1_fixedpoint :
    braunAbsCR1 = (braunAbsLayerSum1 braunAbsCR1 + braunAbsF1 braunAbsCR1) / braunAbsF1 braunAbsCR1 :=
  (braunAbs_cubic braunAbsCR1 braunAbsCR1_ne_two braunAbsCR1_3c5_ne braunAbsF1_CR1_ne).mpr braunAbsCR1_root

/-! ### Trap ratios (multiplicative) -/

/-- L₀ trap: `c·1 ≤ 2` whenever `c ≤ 2`. -/
lemma braunAbs_L0_trap_ratio (c : ℝ) (hc : c ≤ 2) : c * (1 : ℝ) ≤ 2 := by
  simpa using hc

/-- S₀ trap is exact: `c·(1+S₀) = 1+2·S₀` for `c ≠ 2`. -/
lemma braunAbs_S0_trap_ratio (c : ℝ) (h2 : c ≠ 2) :
    c * (1 + braunAbsS0 c) = 1 + 2 * braunAbsS0 c := by
  dsimp [braunAbsS0]
  field_simp [h2]
  ring

/-- F trap is exact: `c·F = Σ + F` (the fixed point, evaluated at c₁). -/
lemma braunAbs_F_trap_ratio :
    braunAbsCR1 * braunAbsF1 braunAbsCR1 = braunAbsLayerSum1 braunAbsCR1 + braunAbsF1 braunAbsCR1 := by
  exact (eq_div_iff braunAbsF1_CR1_ne).mp braunAbsCR1_fixedpoint

end

end OnlineScheduling
