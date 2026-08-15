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
import OnlineScheduling.LowerBounds.BraunGraham2025

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

/-! ### Rational bounds on c₁ -/

/-- c₁ < 7/4. -/
lemma braunAbsCR1_lt_seven_quarters : braunAbsCR1 < 7 / 4 := by
  have hfac : ∀ c : ℝ,
      6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 - (6 * (7 / 4) ^ 3 - 28 * (7 / 4) ^ 2 + 38 * (7 / 4) - 13)
        = (c - 7 / 4) * (6 * c ^ 2 - (35 / 2) * c + 59 / 8) := by
    intro c
    ring
  have hdiff : (braunAbsCR1 - 7 / 4) * (6 * braunAbsCR1 ^ 2 - (35 / 2) * braunAbsCR1 + 59 / 8) = 3 / 32 := by
    calc
      (braunAbsCR1 - 7 / 4) * (6 * braunAbsCR1 ^ 2 - (35 / 2) * braunAbsCR1 + 59 / 8)
          = 6 * braunAbsCR1 ^ 3 - 28 * braunAbsCR1 ^ 2 + 38 * braunAbsCR1 - 13
            - (6 * (7 / 4) ^ 3 - 28 * (7 / 4) ^ 2 + 38 * (7 / 4) - 13) := by rw [hfac braunAbsCR1]
      _ = 0 - (-(3 / 32)) := by rw [braunAbsCR1_root]; norm_num
      _ = 3 / 32 := by norm_num
  have hquad : 6 * braunAbsCR1 ^ 2 - (35 / 2) * braunAbsCR1 + 59 / 8 < 0 := by
    nlinarith [braunAbsCR1_lo, braunAbsCR1_hi]
  have hprod : 0 < (braunAbsCR1 - 7 / 4) * (6 * braunAbsCR1 ^ 2 - (35 / 2) * braunAbsCR1 + 59 / 8) := by
    rw [hdiff]
    norm_num
  rcases mul_pos_iff.mp hprod with hpos | hneg
  · exfalso
    nlinarith [hpos.2, hquad]
  · nlinarith [hneg.1]

/-- 12/7 < c₁. -/
lemma braunAbsCR1_gt_12_7 : (12 / 7 : ℝ) < braunAbsCR1 := by
  have hfac : ∀ c : ℝ,
      6 * c ^ 3 - 28 * c ^ 2 + 38 * c - 13 - (6 * (12 / 7) ^ 3 - 28 * (12 / 7) ^ 2 + 38 * (12 / 7) - 13)
        = (c - 12 / 7) * (6 * c ^ 2 - (124 / 7) * c + 374 / 49) := by
    intro c
    ring
  have hdiff : (braunAbsCR1 - 12 / 7) * (6 * braunAbsCR1 ^ 2 - (124 / 7) * braunAbsCR1 + 374 / 49) = -(29 / 343) := by
    calc
      (braunAbsCR1 - 12 / 7) * (6 * braunAbsCR1 ^ 2 - (124 / 7) * braunAbsCR1 + 374 / 49)
          = 6 * braunAbsCR1 ^ 3 - 28 * braunAbsCR1 ^ 2 + 38 * braunAbsCR1 - 13
            - (6 * (12 / 7) ^ 3 - 28 * (12 / 7) ^ 2 + 38 * (12 / 7) - 13) := by rw [hfac braunAbsCR1]
      _ = 0 - (29 / 343) := by rw [braunAbsCR1_root]; norm_num
      _ = -(29 / 343) := by norm_num
  have hquad : 6 * braunAbsCR1 ^ 2 - (124 / 7) * braunAbsCR1 + 374 / 49 < 0 := by
    nlinarith [braunAbsCR1_lo, braunAbsCR1_hi]
  have hprod : (braunAbsCR1 - 12 / 7) * (6 * braunAbsCR1 ^ 2 - (124 / 7) * braunAbsCR1 + 374 / 49) < 0 := by
    rw [hdiff]
    norm_num
  rcases mul_neg_iff.mp hprod with hpos | hneg
  · nlinarith [hpos.1]
  · exfalso
    nlinarith [hneg.2, hquad]

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

/-- L₁ trap (slack): `c₁·(1+S₀+L₁) ≤ 1+S₀+2·L₁`. -/
lemma braunAbs_L1_slack_identity :
    (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) *
      ((1 + braunAbsS0 braunAbsCR1 + 2 * braunAbsL1 braunAbsCR1) - braunAbsCR1 * (1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1))
      = 3 * braunAbsCR1 ^ 3 - 14 * braunAbsCR1 ^ 2 + 17 * braunAbsCR1 - 3 := by
  dsimp [braunAbsS0, braunAbsL1]
  ring_nf
  have h2 : 2 - braunAbsCR1 ≠ 0 := sub_ne_zero.mpr (Ne.symm braunAbsCR1_ne_two)
  have h3 : -5 + braunAbsCR1 * 3 ≠ 0 := by
    have h := braunAbsCR1_3c5_ne
    ring_nf at h
    exact h
  field_simp [h2, h3]
  ring

lemma braunAbs_L1_trap :
    braunAbsCR1 * (1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1) ≤
      1 + braunAbsS0 braunAbsCR1 + 2 * braunAbsL1 braunAbsCR1 := by
  have hid := braunAbs_L1_slack_identity
  have hpos : 0 < (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) := by
    have h2 : 0 < 2 - braunAbsCR1 := by nlinarith [braunAbsCR1_hi]
    have h3 : 0 < 3 * braunAbsCR1 - 5 := by nlinarith [braunAbsCR1_lo]
    exact mul_pos h2 h3
  have hslack : 0 ≤ 3 * braunAbsCR1 ^ 3 - 14 * braunAbsCR1 ^ 2 + 17 * braunAbsCR1 - 3 := by
    nlinarith [braunAbsCR1_root, braunAbsCR1_lt_seven_quarters]
  have hdiff_nonneg : 0 ≤ (1 + braunAbsS0 braunAbsCR1 + 2 * braunAbsL1 braunAbsCR1) - braunAbsCR1 * (1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1) := by
    exact (mul_le_mul_iff_of_pos_left hpos).mp (by rw [hid]; simpa [mul_zero] using hslack)
  nlinarith [hdiff_nonneg]

/-- S₁ trap (slack): `c₁·(S₁+L₁) ≤ 1+S₀+L₁+2·S₁`. -/
lemma braunAbs_S1_slack_identity :
    (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) *
      ((1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1 + 2 * braunAbsS1 braunAbsCR1) - braunAbsCR1 * (braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1))
      = 6 * braunAbsCR1 ^ 3 - 22 * braunAbsCR1 ^ 2 + 26 * braunAbsCR1 - 10 := by
  dsimp [braunAbsS0, braunAbsL1, braunAbsS1]
  ring_nf
  have h2 : 2 - braunAbsCR1 ≠ 0 := sub_ne_zero.mpr (Ne.symm braunAbsCR1_ne_two)
  have h3 : -5 + braunAbsCR1 * 3 ≠ 0 := by
    have h := braunAbsCR1_3c5_ne
    ring_nf at h
    exact h
  field_simp [h2, h3]
  ring

lemma braunAbs_S1_trap :
    braunAbsCR1 * (braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1) ≤
      1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1 + 2 * braunAbsS1 braunAbsCR1 := by
  have hid := braunAbs_S1_slack_identity
  have hpos : 0 < (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) := by
    have h2 : 0 < 2 - braunAbsCR1 := by nlinarith [braunAbsCR1_hi]
    have h3 : 0 < 3 * braunAbsCR1 - 5 := by nlinarith [braunAbsCR1_lo]
    exact mul_pos h2 h3
  have hslack : 0 ≤ 6 * braunAbsCR1 ^ 3 - 22 * braunAbsCR1 ^ 2 + 26 * braunAbsCR1 - 10 := by
    nlinarith [braunAbsCR1_root, braunAbsCR1_gt_12_7]
  have hdiff_nonneg : 0 ≤ (1 + braunAbsS0 braunAbsCR1 + braunAbsL1 braunAbsCR1 + 2 * braunAbsS1 braunAbsCR1) - braunAbsCR1 * (braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1) := by
    exact (mul_le_mul_iff_of_pos_left hpos).mp (by rw [hid]; simpa [mul_zero] using hslack)
  nlinarith [hdiff_nonneg]

/-! ### OPT upper bounds (packings) -/

/-- Feasibility of the S₁ packing: `4 + 4·S₀ ≤ S₁`. -/
lemma braunAbs_S1_ge_4_4S0 : 4 + 4 * braunAbsS0 braunAbsCR1 ≤ braunAbsS1 braunAbsCR1 := by
  have hid : (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) * (braunAbsS1 braunAbsCR1 - 4 - 4 * braunAbsS0 braunAbsCR1)
      = -3 * braunAbsCR1 ^ 2 - 4 * braunAbsCR1 + 17 := by
    dsimp [braunAbsS0, braunAbsS1]
    ring_nf
    have h2 : 2 - braunAbsCR1 ≠ 0 := sub_ne_zero.mpr (Ne.symm braunAbsCR1_ne_two)
    have h3 : -5 + braunAbsCR1 * 3 ≠ 0 := by
      have h := braunAbsCR1_3c5_ne
      ring_nf at h
      exact h
    field_simp [h2, h3]
    ring
  have hpos : 0 < (2 - braunAbsCR1) * (3 * braunAbsCR1 - 5) := by
    have h2 : 0 < 2 - braunAbsCR1 := by nlinarith [braunAbsCR1_hi]
    have h3 : 0 < 3 * braunAbsCR1 - 5 := by nlinarith [braunAbsCR1_lo]
    exact mul_pos h2 h3
  have hslack : 0 ≤ -3 * braunAbsCR1 ^ 2 - 4 * braunAbsCR1 + 17 := by
    have hfac : -3 * braunAbsCR1 ^ 2 - 4 * braunAbsCR1 + 17 =
        (7 / 4 - braunAbsCR1) * (3 * braunAbsCR1 + 37 / 4) + 13 / 16 := by ring
    rw [hfac]
    have h1 : 0 < 7 / 4 - braunAbsCR1 := by nlinarith [braunAbsCR1_lt_seven_quarters]
    have h2 : 0 < 3 * braunAbsCR1 + 37 / 4 := by nlinarith [braunAbsCR1_lo]
    nlinarith [mul_pos h1 h2]
  have hdiff : 0 ≤ braunAbsS1 braunAbsCR1 - 4 - 4 * braunAbsS0 braunAbsCR1 := by
    exact (mul_le_mul_iff_of_pos_left hpos).mp (by rw [hid]; simpa [mul_zero] using hslack)
  nlinarith [hdiff]

/-- S⁺₁ trap is exact: `c·(S⁺₁+L₁) = Σ + S⁺₁` for all `c ≠ 2, 3c−5 ≠ 0`
    (this is the defining equation of `L₁`). -/
lemma braunAbs_Sp1_trap_ratio (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) :
    c * (braunAbsSp1 c + braunAbsL1 c) = braunAbsLayerSum1 c + braunAbsSp1 c := by
  dsimp [braunAbsSp1, braunAbsL1, braunAbsLayerSum1, braunAbsS0, braunAbsS1]
  ring_nf
  have h3' : -5 + c * 3 ≠ 0 := by
    have h := h3
    ring_nf at h
    exact h
  field_simp [h2, h3']
  ring

/-! ### OPT of the trap witnesses -/

/-- OPT of the L₀ witness (four unit jobs) = 1. -/
lemma braunAbs_opt_L0 : optMakespan (m := 4) (List.replicate 4 (1 : ℝ)) = 1 := by
  apply le_antisymm
  · have hle := optMakespan_le_of_schedule (m := 4) (List.replicate 4 (1 : ℝ))
      (fun _ : Fin 4 => (1 : ℝ)) (diagAssignReplicate (m := 4) (1 : ℝ)) (by
        rw [scheduleLoads_replicate_diag (m := 4) (1 : ℝ)])
    rwa [makespan_const (m := 4)] at hle
  · have hge := optMakespan_ge_avg (m := 4) (List.replicate 4 (1 : ℝ))
    have htot : totalLoad (List.replicate 4 (1 : ℝ)) / ((4 : ℕ) : ℝ) = 1 := by
      dsimp only [totalLoad]
      simp only [List.sum_replicate, nsmul_eq_mul]
      norm_num
    rwa [htot] at hge

/-- OPT of the S₀ witness (L₀×4 ++ S₀×4) = 1 + S₀. -/
lemma braunAbs_opt_S0 (c : ℝ) :
    optMakespan (m := 4) (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c)) = 1 + braunAbsS0 c := by
  apply le_antisymm
  · have hle := optMakespan_le_of_schedule (m := 4) (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c))
      (fun _ : Fin 4 => 1 + braunAbsS0 c)
      (appendAssign (m := 4) (List.replicate 4 (1 : ℝ)) (List.replicate 4 (braunAbsS0 c))
        (diagAssignReplicate (m := 4) (1 : ℝ)) (diagAssignReplicate (m := 4) (braunAbsS0 c))) (by
          ext j
          rw [scheduleLoads_append (m := 4), scheduleLoads_replicate_diag (m := 4) (1 : ℝ),
            scheduleLoads_replicate_diag (m := 4) (braunAbsS0 c)])
    rwa [makespan_const (m := 4)] at hle
  · have hge := optMakespan_ge_avg (m := 4) (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c))
    have htot : totalLoad (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c)) / ((4 : ℕ) : ℝ) = 1 + braunAbsS0 c := by
      dsimp only [totalLoad]
      rw [List.sum_append]
      simp only [List.sum_replicate, nsmul_eq_mul]
      nlinarith
    rwa [htot] at hge

/-- OPT of the L₁ witness (L₀×4 ++ S₀×4 ++ L₁×4) = 1 + S₀ + L₁. -/
lemma braunAbs_opt_L1 (c : ℝ) :
    optMakespan (m := 4) (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c))
      = 1 + braunAbsS0 c + braunAbsL1 c := by
  apply le_antisymm
  · have hle := optMakespan_le_of_schedule (m := 4)
      (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c))
      (fun _ : Fin 4 => 1 + braunAbsS0 c + braunAbsL1 c)
      (appendAssign (m := 4) (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c)) (List.replicate 4 (braunAbsL1 c))
        (appendAssign (m := 4) (List.replicate 4 (1 : ℝ)) (List.replicate 4 (braunAbsS0 c))
          (diagAssignReplicate (m := 4) (1 : ℝ)) (diagAssignReplicate (m := 4) (braunAbsS0 c)))
        (diagAssignReplicate (m := 4) (braunAbsL1 c))) (by
          ext j
          rw [scheduleLoads_append (m := 4), scheduleLoads_append (m := 4),
            scheduleLoads_replicate_diag (m := 4) (1 : ℝ),
            scheduleLoads_replicate_diag (m := 4) (braunAbsS0 c),
            scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c)])
    rwa [makespan_const (m := 4)] at hle
  · have hge := optMakespan_ge_avg (m := 4)
      (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c))
    have htot : totalLoad (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c)) / ((4 : ℕ) : ℝ)
        = 1 + braunAbsS0 c + braunAbsL1 c := by
      dsimp only [totalLoad]
      rw [List.sum_append, List.sum_append]
      simp only [List.sum_replicate, nsmul_eq_mul]
      nlinarith
    rwa [htot] at hge

/-! ### OPT upper bounds for the layer-1 trap witnesses (r = 1) -/

/-- S₀ ≥ 2 (feasibility of the S⁺₁ packing). -/
lemma braunAbsS0_ge_2 : 2 ≤ braunAbsS0 braunAbsCR1 := by
  have h2 : 0 < 2 - braunAbsCR1 := by nlinarith [braunAbsCR1_hi]
  have hid : (2 - braunAbsCR1) * (braunAbsS0 braunAbsCR1 - 2) = 3 * braunAbsCR1 - 5 := by
    dsimp [braunAbsS0]
    field_simp [sub_ne_zero.mpr (Ne.symm braunAbsCR1_ne_two)]
    ring
  have hpos : 0 < (2 - braunAbsCR1) * (braunAbsS0 braunAbsCR1 - 2) := by
    rw [hid]
    nlinarith [braunAbsCR1_lo]
  have hS0 : 0 < braunAbsS0 braunAbsCR1 - 2 := (mul_pos_iff_of_pos_left h2).mp hpos
  nlinarith [hS0]

/-- S₁ = 3·S₀ + 2·L₁ + 2 (identity for all admissible c, used in the F packing). -/
lemma braunAbs_S1_eq_3S0_2L1_2 (c : ℝ) (h2 : c ≠ 2) (h3 : 3 * c - 5 ≠ 0) :
    braunAbsS1 c = 3 * braunAbsS0 c + 2 * braunAbsL1 c + 2 := by
  dsimp [braunAbsS0, braunAbsL1, braunAbsS1]
  have h3' : -5 + c * 3 ≠ 0 := by
    have h := h3
    ring_nf at h
    exact h
  field_simp [h2, h3']
  ring

/-- The S₁ trap witness (15 jobs). -/
def braunAbsS1Witness (c : ℝ) : JobSequence :=
  List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++
  List.replicate 4 (braunAbsL1 c) ++ List.replicate 3 (braunAbsS1 c)

/-- Diagonal assignment of a 3-block to machines 0,1,2. -/
noncomputable def braunAbsDiagAssign3 : Fin 3 → Fin 4 :=
  fun i => ⟨i.1, by omega⟩

/-- Load of a 4-replicate block under the constant assignment to machine `k`. -/
lemma braunAbs_scheduleLoads_replicate4_const (k : Fin 4) (x : ℝ) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 4 x) (fun _ : Fin 4 => k) j =
      if j = k then 4 * x else 0 := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 4, if (fun _ : Fin 4 => k) i = j then (List.replicate 4 x)[i] else 0) =
    if j = k then 4 * x else 0
  rw [Fin.sum_univ_four]
  fin_cases j <;> fin_cases k <;> simp [List.getElem_replicate] <;> ring

/-- Load of a 3-replicate block under the diagonal assignment to 0,1,2. -/
lemma braunAbs_scheduleLoads_replicate3_diag (x : ℝ) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 3 x) braunAbsDiagAssign3 j =
      if j.1 < 3 then x else 0 := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 3, if braunAbsDiagAssign3 i = j then (List.replicate 3 x)[i] else 0) =
    if j.1 < 3 then x else 0
  rw [Fin.sum_univ_three]
  fin_cases j <;> simp [braunAbsDiagAssign3, List.getElem_replicate] <;> ring

/-- Assignment for the S₁ packing (Table 11): L₀,S₀ → machine 3; L₁ diagonal;
    S₁ → machines 0,1,2. -/
noncomputable def braunAbsAssign3S1 (c : ℝ) :
    Fin (braunAbsS1Witness c).length → Fin 4 :=
  appendAssign (m := 4)
    (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c))
    (List.replicate 3 (braunAbsS1 c))
    (appendAssign (m := 4)
      (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c))
      (List.replicate 4 (braunAbsL1 c))
      (appendAssign (m := 4)
        (List.replicate 4 (1 : ℝ))
        (List.replicate 4 (braunAbsS0 c))
        (fun _ => (3 : Fin 4)) (fun _ => (3 : Fin 4)))
      (diagAssignReplicate (m := 4) (braunAbsL1 c)))
    braunAbsDiagAssign3

/-- Loads of the S₁-trap witness packing. -/
lemma braunAbsAssign3S1_loads (c : ℝ) :
    scheduleLoads (m := 4) (braunAbsS1Witness c) (braunAbsAssign3S1 c) 0 = braunAbsL1 c + braunAbsS1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c) (braunAbsAssign3S1 c) 1 = braunAbsL1 c + braunAbsS1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c) (braunAbsAssign3S1 c) 2 = braunAbsL1 c + braunAbsS1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c) (braunAbsAssign3S1 c) 3 = 4 + 4 * braunAbsS0 c + braunAbsL1 c := by
  have hdecomp (j : Fin 4) :
      scheduleLoads (m := 4) (braunAbsS1Witness c) (braunAbsAssign3S1 c) j =
        scheduleLoads (m := 4) (List.replicate 4 (1 : ℝ)) (fun _ : Fin 4 => (3 : Fin 4)) j +
        scheduleLoads (m := 4) (List.replicate 4 (braunAbsS0 c)) (fun _ : Fin 4 => (3 : Fin 4)) j +
        scheduleLoads (m := 4) (List.replicate 4 (braunAbsL1 c)) (diagAssignReplicate (m := 4) (braunAbsL1 c)) j +
        scheduleLoads (m := 4) (List.replicate 3 (braunAbsS1 c)) braunAbsDiagAssign3 j := by
    dsimp only [braunAbsS1Witness, braunAbsAssign3S1]
    rw [scheduleLoads_append (m := 4), scheduleLoads_append (m := 4), scheduleLoads_append (m := 4)]
    rfl
  constructor
  · rw [hdecomp 0, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 0,
      braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (braunAbsS0 c) 0,
      scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c), braunAbs_scheduleLoads_replicate3_diag (braunAbsS1 c) 0]
    simp <;> ring
  constructor
  · rw [hdecomp 1, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 1,
      braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (braunAbsS0 c) 1,
      scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c), braunAbs_scheduleLoads_replicate3_diag (braunAbsS1 c) 1]
    simp <;> ring
  constructor
  · rw [hdecomp 2, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 2,
      braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (braunAbsS0 c) 2,
      scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c), braunAbs_scheduleLoads_replicate3_diag (braunAbsS1 c) 2]
    simp <;> ring
  · rw [hdecomp 3, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 3,
      braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (braunAbsS0 c) 3,
      scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c), braunAbs_scheduleLoads_replicate3_diag (braunAbsS1 c) 3]
    simp <;> ring

/-- OPT of the S₁ trap witness ≤ S₁ + L₁ (Table 11). -/
lemma braunAbs_opt_S1_le :
    optMakespan (m := 4) (braunAbsS1Witness braunAbsCR1) ≤
      braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1 := by
  have hle := optMakespan_le_of_schedule (m := 4) (braunAbsS1Witness braunAbsCR1)
    (scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1) (braunAbsAssign3S1 braunAbsCR1))
    (braunAbsAssign3S1 braunAbsCR1) rfl
  refine le_trans hle ?_
  dsimp only [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  rcases braunAbsAssign3S1_loads braunAbsCR1 with ⟨h0, h1, h2, h3⟩
  fin_cases j
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1) (braunAbsAssign3S1 braunAbsCR1) 0 ≤
      braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h0]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1) (braunAbsAssign3S1 braunAbsCR1) 1 ≤
      braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h1]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1) (braunAbsAssign3S1 braunAbsCR1) 2 ≤
      braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h2]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1) (braunAbsAssign3S1 braunAbsCR1) 3 ≤
      braunAbsS1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h3]
    nlinarith [braunAbs_S1_ge_4_4S0]

/-! ### OPT upper bound for the S⁺₁ trap witness (Table 10) -/

/-- S₀×4 → machines 1,1,2,2 in the S⁺₁ packing. -/
noncomputable def braunAbsAssignS0_1122 : Fin 4 → Fin 4 :=
  fun i => if i.1 < 2 then 1 else 2

/-- Load of a 4-replicate block under the 1,1,2,2 assignment. -/
lemma braunAbs_loads_S0_1122 (x : ℝ) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 4 x) braunAbsAssignS0_1122 j =
      if j = 1 then 2 * x else if j = 2 then 2 * x else 0 := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 4, if braunAbsAssignS0_1122 i = j then (List.replicate 4 x)[i] else 0) =
    if j = 1 then 2 * x else if j = 2 then 2 * x else 0
  rw [Fin.sum_univ_four]
  fin_cases j <;> simp [braunAbsAssignS0_1122, List.getElem_replicate] <;> ring

/-- S₁×3 → machines 1,2,3 in the S⁺₁ packing. -/
noncomputable def braunAbsAssign3_123 : Fin 3 → Fin 4 :=
  fun i => ⟨i.1 + 1, by omega⟩

/-- Load of a 3-replicate block under the 1,2,3 assignment. -/
lemma braunAbs_loads_3_123 (x : ℝ) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 3 x) braunAbsAssign3_123 j =
      if j = 0 then 0 else x := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 3, if braunAbsAssign3_123 i = j then (List.replicate 3 x)[i] else 0) =
    if j = 0 then 0 else x
  rw [Fin.sum_univ_three]
  fin_cases j <;> simp [braunAbsAssign3_123, List.getElem_replicate] <;> ring

/-- Assignment for the S⁺₁ packing (Table 10): Sp₁ → 0; L₁ diagonal; S₁ → 1,2,3;
    S₀ → 1,1,2,2; L₀ → 3. -/
noncomputable def braunAbsAssignSp1 (c : ℝ) :
    Fin (braunAbsS1Witness c ++ [braunAbsSp1 c]).length → Fin 4 :=
  appendAssign (m := 4) (braunAbsS1Witness c) [braunAbsSp1 c]
    (appendAssign (m := 4)
      (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c) ++ List.replicate 4 (braunAbsL1 c))
      (List.replicate 3 (braunAbsS1 c))
      (appendAssign (m := 4)
        (List.replicate 4 (1 : ℝ) ++ List.replicate 4 (braunAbsS0 c))
        (List.replicate 4 (braunAbsL1 c))
        (appendAssign (m := 4)
          (List.replicate 4 (1 : ℝ))
          (List.replicate 4 (braunAbsS0 c))
          (fun _ => (3 : Fin 4)) braunAbsAssignS0_1122)
        (diagAssignReplicate (m := 4) (braunAbsL1 c)))
      braunAbsAssign3_123)
    (fun _ : Fin 1 => (0 : Fin 4))

/-- Loads of the S⁺₁-trap witness packing. -/
lemma braunAbsAssignSp1_loads (c : ℝ) :
    scheduleLoads (m := 4) (braunAbsS1Witness c ++ [braunAbsSp1 c]) (braunAbsAssignSp1 c) 0 = braunAbsL1 c + braunAbsSp1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c ++ [braunAbsSp1 c]) (braunAbsAssignSp1 c) 1 = 2 * braunAbsS0 c + braunAbsL1 c + braunAbsS1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c ++ [braunAbsSp1 c]) (braunAbsAssignSp1 c) 2 = 2 * braunAbsS0 c + braunAbsL1 c + braunAbsS1 c ∧
    scheduleLoads (m := 4) (braunAbsS1Witness c ++ [braunAbsSp1 c]) (braunAbsAssignSp1 c) 3 = 4 + braunAbsL1 c + braunAbsS1 c := by
  have hdecomp (j : Fin 4) :
      scheduleLoads (m := 4) (braunAbsS1Witness c ++ [braunAbsSp1 c]) (braunAbsAssignSp1 c) j =
        scheduleLoads (m := 4) (List.replicate 4 (1 : ℝ)) (fun _ : Fin 4 => (3 : Fin 4)) j +
        scheduleLoads (m := 4) (List.replicate 4 (braunAbsS0 c)) braunAbsAssignS0_1122 j +
        scheduleLoads (m := 4) (List.replicate 4 (braunAbsL1 c)) (diagAssignReplicate (m := 4) (braunAbsL1 c)) j +
        scheduleLoads (m := 4) (List.replicate 3 (braunAbsS1 c)) braunAbsAssign3_123 j +
        scheduleLoads (m := 4) [braunAbsSp1 c] (fun _ : Fin 1 => (0 : Fin 4)) j := by
    dsimp only [braunAbsS1Witness, braunAbsAssignSp1]
    rw [scheduleLoads_append (m := 4), scheduleLoads_append (m := 4), scheduleLoads_append (m := 4),
      scheduleLoads_append (m := 4)]
    rfl
  constructor
  · rw [hdecomp 0, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 0,
      braunAbs_loads_S0_1122 (braunAbsS0 c) 0, scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c),
      braunAbs_loads_3_123 (braunAbsS1 c) 0, scheduleLoads_singleton (braunAbsSp1 c) (fun _ : Fin 1 => (0 : Fin 4)) 0]
    simp <;> ring
  constructor
  · rw [hdecomp 1, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 1,
      braunAbs_loads_S0_1122 (braunAbsS0 c) 1, scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c),
      braunAbs_loads_3_123 (braunAbsS1 c) 1, scheduleLoads_singleton (braunAbsSp1 c) (fun _ : Fin 1 => (0 : Fin 4)) 1]
    simp <;> ring
  constructor
  · rw [hdecomp 2, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 2,
      braunAbs_loads_S0_1122 (braunAbsS0 c) 2, scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c),
      braunAbs_loads_3_123 (braunAbsS1 c) 2, scheduleLoads_singleton (braunAbsSp1 c) (fun _ : Fin 1 => (0 : Fin 4)) 2]
    simp <;> ring
  · rw [hdecomp 3, braunAbs_scheduleLoads_replicate4_const (3 : Fin 4) (1 : ℝ) 3,
      braunAbs_loads_S0_1122 (braunAbsS0 c) 3, scheduleLoads_replicate_diag (m := 4) (braunAbsL1 c),
      braunAbs_loads_3_123 (braunAbsS1 c) 3, scheduleLoads_singleton (braunAbsSp1 c) (fun _ : Fin 1 => (0 : Fin 4)) 3]
    simp <;> ring

/-- OPT of the S⁺₁ trap witness ≤ S⁺₁ + L₁ (Table 10). -/
lemma braunAbs_opt_Sp1_le :
    optMakespan (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) ≤
      braunAbsSp1 braunAbsCR1 + braunAbsL1 braunAbsCR1 := by
  have hle := optMakespan_le_of_schedule (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1])
    (scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) (braunAbsAssignSp1 braunAbsCR1))
    (braunAbsAssignSp1 braunAbsCR1) rfl
  refine le_trans hle ?_
  dsimp only [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  rcases braunAbsAssignSp1_loads braunAbsCR1 with ⟨h0, h1, h2, h3⟩
  fin_cases j
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) (braunAbsAssignSp1 braunAbsCR1) 0 ≤
      braunAbsSp1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h0]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) (braunAbsAssignSp1 braunAbsCR1) 1 ≤
      braunAbsSp1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h1]
    dsimp [braunAbsSp1]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) (braunAbsAssignSp1 braunAbsCR1) 2 ≤
      braunAbsSp1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h2]
    dsimp [braunAbsSp1]
    nlinarith
  · change scheduleLoads (m := 4) (braunAbsS1Witness braunAbsCR1 ++ [braunAbsSp1 braunAbsCR1]) (braunAbsAssignSp1 braunAbsCR1) 3 ≤
      braunAbsSp1 braunAbsCR1 + braunAbsL1 braunAbsCR1
    rw [h3]
    dsimp [braunAbsSp1]
    nlinarith [braunAbsS0_ge_2]

end

end OnlineScheduling
