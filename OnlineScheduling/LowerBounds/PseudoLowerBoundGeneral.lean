/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Pseudo Lower Bounds (Tan & Li, 2015), general m

General-m analytic infrastructure for the pseudo-lower-bound adversary of
Theorem 3.1 in Tan & Li, "Pseudo lower bounds for online parallel machine
scheduling", Operations Research Letters 43 (2015) 489-494.

For m >= 4 the paper defines
  f_i^(m)(x) = ((m-1-x)/m)^i                      (i = 1..m)
  g_i^(m)(x) = (1/i)(sum_{j=1..i} f_j^(m)(x) - (m-1-mx))   (i = 1..t, t = floor(m/2))
with the identities
  (i+1)g_{i+1} - i g_i = f_{i+1}                 (3)
  sum_{j=1..i} f_j = m/(1+x) (f_1 - f_{i+1})     (4)
  g_i = m/((1+x)i) (x^2 - f_{i+1})               (5)
The unique root x_i of g_i(x) = 1/2 in [5/7, (m+t)/(2m-t)] and the index
q_m = min {i | f_{i+1}(x_i) <= 1/2 <= f_i(x_i)} determine
  beta_m = x_{q_m},  alpha = (3+sqrt 57)/12,  gamma_m = min(beta_m, alpha).

This file formalizes the definitions and the elementary algebraic
identities; the root machinery and the adversary construction live here too.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset
open BigOperators

namespace OnlineScheduling

/-- `alpha = (3 + sqrt 57) / 12`, the positive solution of `x(x-1/2) = 1/3`. -/
noncomputable def tanAlpha : ℝ := (3 + Real.sqrt 57) / 12

/-- `c^(m)(x) = (m-1-x)/m`, the base of the geometric sequence `f_i`. -/
noncomputable def cVal (m : ℕ) (x : ℝ) : ℝ :=
  ((m : ℝ) - 1 - x) / (m : ℝ)

/-- `f_i^(m)(x) = ((m-1-x)/m)^i` (equation (1) of the paper). -/
noncomputable def fVal (m : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  cVal m x ^ i

/-- `g_i^(m)(x) = (1/i) (sum_{j=1..i} f_j^(m)(x) - (m-1-mx))`
    (equation (2) of the paper). -/
noncomputable def gVal (m : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  ((∑ j ∈ Finset.Icc 1 i, fVal m x j) - ((m : ℝ) - 1 - (m : ℝ) * x)) / (i : ℝ)

/-- `x_1^(m) = (2m^2-3m+2)/(2m^2-2)`, the root of `g_1 = 1/2` (paper (8)). -/
noncomputable def x1Val (m : ℕ) : ℝ :=
  (2 * (m : ℝ) ^ 2 - 3 * (m : ℝ) + 2) / (2 * (m : ℝ) ^ 2 - 2)

/-- `f_{i+1} = f_i * f_1`, i.e. `c^(i+1) = c^i * c`. -/
lemma fVal_succ (m : ℕ) (x : ℝ) (i : ℕ) :
    fVal m x (i + 1) = fVal m x i * fVal m x 1 := by
  dsimp [fVal]
  rw [pow_succ]
  ring

/-- `1 - f_1^(m)(x) = (1+x)/m`. -/
lemma fVal_one_sub (m : ℕ) (hm : m ≠ 0) (x : ℝ) :
    1 - fVal m x 1 = (1 + x) / (m : ℝ) := by
  dsimp [fVal, cVal]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp [hm']
  ring

/-- `i * g_i = sum_{j=1..i} f_j - (m-1-mx)` for `i != 0`. -/
lemma gVal_mul (m : ℕ) (x : ℝ) (i : ℕ) (hi : i ≠ 0) :
    ((i : ℕ) : ℝ) * gVal m x i =
      (∑ j ∈ Finset.Icc 1 i, fVal m x j) - ((m : ℝ) - 1 - (m : ℝ) * x) := by
  dsimp [gVal]
  have hne : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  rw [mul_div_cancel₀ _ hne]

/-- Identity (3): `(i+1)g_{i+1} - i g_i = f_{i+1}` for `i != 0`. -/
lemma gVal_rec (m : ℕ) (x : ℝ) (i : ℕ) (hi : i ≠ 0) :
    ((i + 1 : ℕ) : ℝ) * gVal m x (i + 1) - ((i : ℕ) : ℝ) * gVal m x i =
      fVal m x (i + 1) := by
  rw [gVal_mul m x (i + 1) (by omega), gVal_mul m x i hi]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := i) (by omega)]
  ring

/-- Identity (4): geometric sum of the `f_j` (needs `1+x != 0`). -/
lemma fVal_sum_geometric (m : ℕ) (x : ℝ) (i : ℕ) (hx : 1 + x ≠ 0) (hm : m ≠ 0) :
    (∑ j ∈ Finset.Icc 1 i, fVal m x j) =
      (m : ℝ) / (1 + x) * (fVal m x 1 - fVal m x (i + 1)) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := i) (by omega)]
      rw [ih]
      have hf : fVal m x (i + 2) = fVal m x (i + 1) * fVal m x 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fVal_succ m x (i + 1)
      rw [hf]
      have hsub : (m : ℝ) * (1 - fVal m x 1) = 1 + x := by
        rw [fVal_one_sub m hm x]
        have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        field_simp [hm']
      field_simp [hx]
      rw [← hsub]
      ring

/-- Identity (5): closed form `g_i = m/((1+x)i) * (x^2 - f_{i+1})`. -/
lemma gVal_closed (m : ℕ) (hm : m ≠ 0) (x : ℝ) (i : ℕ) (hi : i ≠ 0) (hx : 1 + x ≠ 0) :
    gVal m x i = (m : ℝ) / ((1 + x) * (i : ℝ)) * (x ^ 2 - fVal m x (i + 1)) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hf1 : (m : ℝ) * fVal m x 1 = (m : ℝ) - 1 - x := by
    dsimp [fVal, cVal]
    field_simp [hm']
  have hsum := fVal_sum_geometric m x i hx hm
  have hmul := gVal_mul m x i hi
  calc
    gVal m x i = (1 / (i : ℝ)) * (((i : ℕ) : ℝ) * gVal m x i) := by
      field_simp [hi']
    _ = (1 / (i : ℝ)) *
        ((∑ j ∈ Finset.Icc 1 i, fVal m x j) - ((m : ℝ) - 1 - (m : ℝ) * x)) := by
      rw [hmul]
    _ = (1 / (i : ℝ)) *
        ((m : ℝ) / (1 + x) * (fVal m x 1 - fVal m x (i + 1)) - ((m : ℝ) - 1 - (m : ℝ) * x)) := by
      rw [hsum]
    _ = (m : ℝ) / ((1 + x) * (i : ℝ)) * (x ^ 2 - fVal m x (i + 1)) := by
      field_simp [hx, hi', hm']
      nlinarith [hf1]

/-- Equation (7): `g_1(x) = ((m-1)/m)((m+1)x - (m-1))`. -/
lemma gVal_one (m : ℕ) (hm : m ≠ 0) (x : ℝ) :
    gVal m x 1 = ((m : ℝ) - 1) / (m : ℝ) * (((m : ℝ) + 1) * x - ((m : ℝ) - 1)) := by
  dsimp [gVal]
  rw [show (∑ j ∈ Finset.Icc 1 1, fVal m x j) = fVal m x 1 by
    rw [Finset.sum_Icc_succ_top (a := 1) (b := 0) (by omega)]
    simp]
  dsimp [fVal, cVal]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp [hm']
  ring

/-- `g_1(x) = 1/2` iff `x = x_1^(m)` (paper (8)). -/
lemma gVal_one_eq_half (m : ℕ) (hm : m ≠ 0) (hm1 : m ≠ 1) (x : ℝ) :
    gVal m x 1 = 1 / 2 ↔ x = x1Val m := by
  have hm2 : 2 ≤ m := by omega
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hmm1 : (m : ℝ) - 1 ≠ 0 := by nlinarith
  have hm2m1 : 2 * ((m : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith [hm2r]
  have hm2m1' : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [hm2r]
  rw [gVal_one m hm x]
  constructor
  · intro h
    have hlin : 2 * ((m : ℝ) ^ 2 - 1) * x = 2 * (m : ℝ) ^ 2 - 3 * (m : ℝ) + 2 := by
      field_simp [hm', hmm1] at h
      nlinarith
    rw [show x = x1Val m by
      dsimp [x1Val]
      field_simp [hm2m1, hm2m1']
      nlinarith [hlin]]
  · intro hx
    rw [hx]
    dsimp [x1Val]
    field_simp [hm', hmm1, hm2m1, hm2m1']
    ring

/-- `f_1(x_1^(m)) = (2m^2-4m+1)/(2(m^2-1))` (paper (8)). -/
lemma fVal_one_x1 (m : ℕ) (hm : m ≠ 0) (hm1 : m ≠ 1) :
    fVal m (x1Val m) 1 =
      (2 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 1) / (2 * ((m : ℝ) ^ 2 - 1)) := by
  have hm2 : 2 ≤ m := by omega
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm2m1 : 2 * ((m : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith [hm2r]
  have hm2m1' : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [hm2r]
  dsimp [fVal, cVal, x1Val]
  field_simp [hm', hm2m1, hm2m1']
  ring

/-- If `0 <= a < b` then `a^n < b^n` for `n != 0` (helper for monotonicity). -/
private lemma pow_lt_pow_left_of_nonneg {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hn : n ≠ 0) : a ^ n < b ^ n := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  clear hn
  induction k with
  | zero => simpa using hab
  | succ k ih =>
      have hpow : a ^ (k + 1) < b ^ (k + 1) := ih
      have hapow : 0 ≤ a ^ (k + 1) := pow_nonneg ha (k + 1)
      have hbpow : 0 < b ^ (k + 1) := pow_pos (lt_of_le_of_lt ha hab) (k + 1)
      have hmul1 : a ^ (k + 1) * a ≤ b ^ (k + 1) * a :=
        mul_le_mul_of_nonneg_right hpow.le ha
      have hmul2 : b ^ (k + 1) * a < b ^ (k + 1) * b :=
        mul_lt_mul_of_pos_left hab hbpow
      calc
        a ^ (k + 2) = a ^ (k + 1) * a := by
          simpa using pow_succ a (k + 1)
        _ ≤ b ^ (k + 1) * a := hmul1
        _ < b ^ (k + 1) * b := hmul2
        _ = b ^ (k + 2) := by
          conv_rhs =>
            rw [show k + 2 = (k + 1) + 1 by omega]
            rw [pow_succ]

/-- Lemma 2.1(i): `f_i^(m)` is strictly decreasing on `[0,1]` for `i != 0`. -/
lemma fVal_strictAntiOn {m : ℕ} (hm : 2 ≤ m) (i : ℕ) (hi : i ≠ 0) :
    StrictAntiOn (fun x : ℝ => fVal m x i) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  dsimp [fVal, cVal]
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hc : ((m : ℝ) - 1 - y) / (m : ℝ) < ((m : ℝ) - 1 - x) / (m : ℝ) := by
    have hnum : (m : ℝ) - 1 - y < (m : ℝ) - 1 - x := by nlinarith
    have hinv : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hm_pos
    simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_right hnum hinv
  have hc_nonneg : 0 ≤ ((m : ℝ) - 1 - y) / (m : ℝ) := by
    have hle : 0 ≤ (m : ℝ) - 1 - y := by nlinarith [hy.2]
    exact div_nonneg hle (le_of_lt hm_pos)
  exact pow_lt_pow_left_of_nonneg hc_nonneg hc hi

/-- `c^(m)` is differentiable. -/
@[fun_prop] lemma cVal_differentiableAt (m : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => cVal m y) x := by
  dsimp [cVal]
  fun_prop

/-- `f_j^(m)` is differentiable. -/
@[fun_prop] lemma fVal_differentiableAt (m : ℕ) (j : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => fVal m y j) x := by
  dsimp [fVal, cVal]
  fun_prop

/-- `f_j^(m)` is continuous. -/
@[fun_prop] lemma fVal_continuous (m : ℕ) (j : ℕ) : Continuous (fun x : ℝ => fVal m x j) := by
  dsimp [fVal, cVal]
  fun_prop

/-- A finite sum of the `f_j^(m)` is differentiable. -/
lemma fVal_sum_differentiableAt (m : ℕ) (i : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => ∑ j ∈ Finset.Icc 1 i, fVal m y j) x := by
  fun_prop

/-- `g_i^(m)` is differentiable at every point when `i != 0`. -/
lemma gVal_differentiableAt (m : ℕ) (i : ℕ) (hi : i ≠ 0) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => gVal m y i) x := by
  dsimp [gVal]
  have hnum : DifferentiableAt ℝ
      (fun y : ℝ => (∑ j ∈ Finset.Icc 1 i, fVal m y j) - ((m : ℝ) - 1 - (m : ℝ) * y)) x := by
    fun_prop
  have hden : DifferentiableAt ℝ (fun _ : ℝ => (i : ℝ)) x := differentiableAt_const (i : ℝ)
  have hden0 : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  exact hnum.div hden hden0

/-- `g_i^(m)` is continuous on `[0,1]` when `i != 0`. -/
lemma gVal_continuousOn (m : ℕ) (i : ℕ) (hi : i ≠ 0) :
    ContinuousOn (fun x : ℝ => gVal m x i) (Set.Icc (0 : ℝ) 1) := by
  have hnum : Continuous
      (fun x : ℝ => (∑ j ∈ Finset.Icc 1 i, fVal m x j) - ((m : ℝ) - 1 - (m : ℝ) * x)) := by
    fun_prop
  have hden : Continuous fun _ : ℝ => (i : ℝ) := continuous_const
  have hden0 : ∀ x : ℝ, (i : ℝ) ≠ 0 := fun _ => by exact_mod_cast hi
  exact (hnum.div hden hden0).continuousOn

/-- Derivative of `c^(m)(x) = (m-1-x)/m`. -/
lemma cVal_deriv (m : ℕ) (x : ℝ) : deriv (fun y : ℝ => cVal m y) x = -1 / (m : ℝ) := by
  dsimp [cVal]
  rw [deriv_div_const]
  rw [deriv_const_sub_id]

/-- Derivative of `f_j^(m)(x)`. -/
lemma fVal_deriv (m : ℕ) (j : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => fVal m y j) x = - (j : ℝ) / (m : ℝ) * fVal m x (j - 1) := by
  dsimp [fVal]
  change deriv ((fun y : ℝ => cVal m y) ^ j) x = - (j : ℝ) / (m : ℝ) * cVal m x ^ (j - 1)
  rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => cVal m y) x) j]
  rw [cVal_deriv]
  ring_nf

/-- Derivative of `g_i^(m)(x)`. -/
lemma gVal_deriv (m : ℕ) (x : ℝ) (i : ℕ) :
    deriv (fun y : ℝ => gVal m y i) x =
      ((∑ j ∈ Finset.Icc 1 i, - (j : ℝ) / (m : ℝ) * fVal m x (j - 1)) + (m : ℝ)) / (i : ℝ) := by
  dsimp [gVal]
  rw [deriv_div_const]
  rw [deriv_fun_sub
    (fVal_sum_differentiableAt m i x)
    (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (m : ℝ) - 1 - (m : ℝ) * y) x)]
  rw [deriv_fun_sum]
  · have hC : deriv (fun y : ℝ => (m : ℝ) - 1 - (m : ℝ) * y) x = - (m : ℝ) := by
      rw [deriv_const_sub]
      rw [deriv_const_mul_id]
    simp_rw [fVal_deriv]
    rw [hC]
    ring
  · intro j hj
    exact fVal_differentiableAt m j x

/-- On `(0,1)` the derivative of `g_i^(m)` is positive when `1 <= i <= m/2`
    (Lemma 2.1(ii), via `(g_i)' >= (m-i)/i > 0`). -/
lemma gVal_deriv_pos {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 0 < i) (hi_le : i ≤ m / 2)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < deriv (fun y : ℝ => gVal m y i) x := by
  rw [gVal_deriv]
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hx1 : x < 1 := hx.2
  have hx0 : 0 < x := hx.1
  have hc_pos : 0 < cVal m x := by
    dsimp [cVal]
    have hnum : 0 < (m : ℝ) - 1 - x := by nlinarith [hmr, hx1]
    exact div_pos hnum hm_pos
  have hc_le_one : cVal m x ≤ 1 := by
    dsimp [cVal]
    have hnum : (m : ℝ) - 1 - x ≤ (m : ℝ) := by nlinarith [hx0]
    exact (div_le_one₀ hm_pos).2 hnum
  have hfj : ∀ j ∈ Finset.Icc 1 i, -1 ≤ - (j : ℝ) / (m : ℝ) * fVal m x (j - 1) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_le_m : j ≤ m := by
      have hj_le_i : j ≤ i := (Finset.mem_Icc.mp hj).2
      omega
    have hpow_nonneg : 0 ≤ fVal m x (j - 1) := by
      dsimp [fVal]
      exact pow_nonneg (le_of_lt hc_pos) (j - 1)
    have hpow_le_one : fVal m x (j - 1) ≤ 1 := by
      dsimp [fVal]
      exact pow_le_one₀ (le_of_lt hc_pos) hc_le_one
    have hjm : (j : ℝ) / (m : ℝ) ≤ 1 := (div_le_one₀ hm_pos).2 (by exact_mod_cast hj_le_m)
    have hj0 : 0 ≤ j := by omega
    have hfrac_nonneg : 0 ≤ (j : ℝ) / (m : ℝ) :=
      div_nonneg (by exact_mod_cast hj0) (le_of_lt hm_pos)
    have hprod_le : (j : ℝ) / (m : ℝ) * fVal m x (j - 1) ≤ 1 :=
      mul_le_one₀ hjm hpow_nonneg hpow_le_one
    have hprod_le' : -1 ≤ - ((j : ℝ) / (m : ℝ) * fVal m x (j - 1)) := by
      nlinarith [hprod_le]
    simpa [neg_div, neg_mul, mul_neg] using hprod_le'
  have hsum_ge : - (i : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 i, - (j : ℝ) / (m : ℝ) * fVal m x (j - 1) := by
    calc
      - (i : ℝ) = ∑ j ∈ Finset.Icc 1 i, (-1 : ℝ) := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc 1 i).card = i := by simp
        rw [hcard]
        simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Icc 1 i, - (j : ℝ) / (m : ℝ) * fVal m x (j - 1) :=
        Finset.sum_le_sum (fun j hj => hfj j hj)
  have hi2 : 2 * i ≤ m := by omega
  have hi2r : (2 : ℝ) * (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi2
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hm_i_pos : 0 < (m : ℝ) - (i : ℝ) := by nlinarith [hmr, hi2r, hi_pos]
  have hsum_pos :
      0 < (∑ j ∈ Finset.Icc 1 i, - (j : ℝ) / (m : ℝ) * fVal m x (j - 1)) + (m : ℝ) := by
    nlinarith [hsum_ge, hm_i_pos]
  exact div_pos hsum_pos hi_pos

/-- Lemma 2.1(ii): `g_i^(m)` is strictly increasing on `[0,1]` for `1 <= i <= t`. -/
lemma gVal_strictMonoOn {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 0 < i) (hi_le : i ≤ m / 2) :
    StrictMonoOn (fun x : ℝ => gVal m x i) (Set.Icc (0 : ℝ) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) (gVal_continuousOn m i (by omega)) ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hx
    exact gVal_deriv_pos hm i hi hi_le hx'

/-! ### Lemma 2.2: the root `x_i^(m)` of `g_i = 1/2` -/

/-- `t = floor(m/2)`, the upper index bound in the paper. -/
def tVal (m : ℕ) : ℕ := m / 2

/-- The upper endpoint `(m+t)/(2m-t)` of the interval in Lemma 2.2. -/
noncomputable def topVal (m : ℕ) : ℝ :=
  ((m : ℝ) + (tVal m : ℝ)) / (2 * (m : ℝ) - (tVal m : ℝ))

lemma tVal_two_le (m : ℕ) : 2 * tVal m ≤ m := by
  dsimp [tVal]
  omega

lemma tVal_pos {m : ℕ} (hm : 4 ≤ m) : 0 < tVal m := by
  dsimp [tVal]
  omega

lemma topVal_le_one {m : ℕ} (hm : 4 ≤ m) : topVal m ≤ 1 := by
  have htwo : 2 * (tVal m : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast tVal_two_le m
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden_pos : 0 < 2 * (m : ℝ) - (tVal m : ℝ) := by nlinarith [htwo, hm_pos]
  have hnum : (m : ℝ) + (tVal m : ℝ) ≤ 2 * (m : ℝ) - (tVal m : ℝ) := by nlinarith [htwo]
  dsimp [topVal]
  exact (div_le_one₀ hden_pos).2 hnum

lemma five_seven_le_top {m : ℕ} (hm : 4 ≤ m) : (5 / 7 : ℝ) ≤ topVal m := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have h4t : (m : ℕ) ≤ 4 * tVal m := by
    dsimp [tVal]
    omega
  have h4tr : (m : ℝ) ≤ 4 * (tVal m : ℝ) := by exact_mod_cast h4t
  have hden_pos : 0 < 2 * (m : ℝ) - (tVal m : ℝ) := by
    have htwo : 2 * (tVal m : ℝ) ≤ (m : ℝ) := by exact_mod_cast tVal_two_le m
    nlinarith [htwo, hm_pos]
  dsimp [topVal]
  -- 5/7 <= (m+t)/(2m-t)  <=>  3m <= 12t
  rw [le_div_iff₀ hden_pos]
  nlinarith [h4tr]

/-- At `x = 5/7` we have `g_i <= 1/2` (first half of Lemma 2.2). -/
lemma gVal_lower_5_7 {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ m / 2) :
    gVal m (5 / 7 : ℝ) i ≤ 1 / 2 := by
  have hi' : i ≠ 0 := by omega
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hf1 : fVal m (5 / 7 : ℝ) 1 = (7 * (m : ℝ) - 12) / (7 * (m : ℝ)) := by
    dsimp [fVal, cVal]
    field_simp [hm_pos.ne']
    ring
  have hc_pos : 0 < cVal m (5 / 7 : ℝ) := by
    dsimp [cVal]
    have hnum : 0 < (m : ℝ) - 1 - 5 / 7 := by nlinarith [hmr]
    exact div_pos hnum hm_pos
  have hc_le : cVal m (5 / 7 : ℝ) ≤ 1 := by
    dsimp [cVal]
    have hnum : (m : ℝ) - 1 - 5 / 7 ≤ (m : ℝ) := by nlinarith
    exact (div_le_one₀ hm_pos).2 hnum
  have hf_j_le : ∀ j ∈ Finset.Icc 1 i, fVal m (5 / 7 : ℝ) j ≤ fVal m (5 / 7 : ℝ) 1 := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    dsimp [fVal]
    simp [pow_one]
    have hj_eq : j = (j - 1) + 1 := by omega
    calc
      cVal m (5 / 7 : ℝ) ^ j = cVal m (5 / 7 : ℝ) ^ ((j - 1) + 1) := by
        conv_lhs => rw [hj_eq]
      _ = cVal m (5 / 7 : ℝ) ^ (j - 1) * cVal m (5 / 7 : ℝ) := by rw [pow_succ]
      _ ≤ 1 * cVal m (5 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt hc_pos) hc_le) (le_of_lt hc_pos)
      _ = cVal m (5 / 7 : ℝ) := by ring
  have hsum_le :
      (∑ j ∈ Finset.Icc 1 i, fVal m (5 / 7 : ℝ) j) ≤ (i : ℝ) * fVal m (5 / 7 : ℝ) 1 := by
    calc
      (∑ j ∈ Finset.Icc 1 i, fVal m (5 / 7 : ℝ) j)
          ≤ (∑ j ∈ Finset.Icc 1 i, fVal m (5 / 7 : ℝ) 1) :=
            Finset.sum_le_sum (fun j hj => hf_j_le j hj)
      _ = (i : ℝ) * fVal m (5 / 7 : ℝ) 1 := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc 1 i).card = i := by simp
        rw [hcard]
        simp [nsmul_eq_mul]
  have hC : (m : ℝ) - 1 - (m : ℝ) * (5 / 7) = (2 * (m : ℝ) - 7) / 7 := by ring
  have hmul := gVal_mul m (5 / 7 : ℝ) i hi'
  have hmain : (i : ℝ) * gVal m (5 / 7 : ℝ) i ≤ (i : ℝ) * (1 / 2) := by
    calc
      (i : ℝ) * gVal m (5 / 7 : ℝ) i
          = (∑ j ∈ Finset.Icc 1 i, fVal m (5 / 7 : ℝ) j) - ((m : ℝ) - 1 - (m : ℝ) * (5 / 7)) := hmul
      _ ≤ (i : ℝ) * fVal m (5 / 7 : ℝ) 1 - ((m : ℝ) - 1 - (m : ℝ) * (5 / 7)) := by
            nlinarith [hsum_le]
      _ = (i : ℝ) * ((7 * (m : ℝ) - 12) / (7 * (m : ℝ))) - (2 * (m : ℝ) - 7) / 7 := by
            rw [hf1, hC]
      _ ≤ (i : ℝ) / 2 := by
            have hi2 : 2 * i ≤ m := by omega
            have hi2r : (2 : ℝ) * (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi2
            have hi_r : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
            have hpoly : 2 * (i : ℝ) * (7 * (m : ℝ) - 12) - 2 * (m : ℝ) * (2 * (m : ℝ) - 7)
                ≤ 7 * (m : ℝ) * (i : ℝ) := by
              nlinarith [hi2r, hmr, hi_r]
            field_simp [hm_pos.ne']
            nlinarith [hpoly]
      _ = (i : ℝ) * (1 / 2) := by ring
  have hdiv : gVal m (5 / 7 : ℝ) i ≤ 1 / 2 := by
    have hmain' : gVal m (5 / 7 : ℝ) i * (i : ℝ) ≤ (1 / 2) * (i : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi
    nlinarith [hmain', hi_pos]
  exact hdiv

/-- Bernoulli-type quadratic bound: `(1-x)^n <= 1 - nx + n(n-1)/2 x^2` for `0 <= x <= 1`. -/
lemma bernoulli_quadratic {n : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ n ≤ 1 - (n : ℝ) * x + (n.choose 2 : ℝ) * x ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx0' : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      calc
        (1 - x) ^ (n + 1) = (1 - x) ^ n * (1 - x) := by rw [pow_succ]
        _ ≤ (1 - (n : ℝ) * x + (n.choose 2 : ℝ) * x ^ 2) * (1 - x) :=
          mul_le_mul_of_nonneg_right ih hx0'
        _ ≤ 1 - ((n + 1 : ℕ) : ℝ) * x + ((n + 1).choose 2 : ℝ) * x ^ 2 := by
          have hch : ((n + 1).choose 2 : ℝ) = (n.choose 2 : ℝ) + (n : ℝ) := by
            have h := Nat.choose_succ_succ n 1
            have h' : (n + 1).choose 2 = n + n.choose 2 := by
              simpa [Nat.choose_one_right] using h
            have h'' : (n + 1).choose 2 = n.choose 2 + n := by omega
            exact_mod_cast h''
          have hC0 : 0 ≤ (n.choose 2 : ℝ) := by exact_mod_cast (Nat.zero_le (n.choose 2))
          have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
          have hprod : 0 ≤ (n.choose 2 : ℝ) * x ^ 3 := mul_nonneg hC0 hx3
          push_cast
          nlinarith [hch, hprod]

/-- `(n+1) choose 2 = n(n+1)/2`, as reals. -/
private lemma choose_two_succ (n : ℕ) :
    ((n + 1).choose 2 : ℝ) = ((n + 1 : ℝ) * (n : ℝ)) / 2 := by
  have h2m : 2 * (n + 1).choose 2 = (n + 1) * n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hrec : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Nat.choose_succ_succ (n + 1) 1
        have hR : (2 : ℝ) * ((n + 2).choose 2 : ℝ) =
            ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
          rw [hrec]
          have hihR : (2 : ℝ) * ((n + 1).choose 2 : ℝ) = ((n + 1 : ℕ) : ℝ) * (n : ℝ) := by
            exact_mod_cast ih
          have hihR' : 2 * ((n + 1).choose 2 : ℝ) = (n : ℝ) * (n : ℝ) + (n : ℝ) := by
            rw [hihR]
            push_cast
            ring
          push_cast
          calc
            2 * (↑((n + 1).choose 2) + ((↑n : ℝ) + 1))
                = 2 * ↑((n + 1).choose 2) + 2 * ((↑n : ℝ) + 1) := by ring
            _ = ((↑n : ℝ) * (↑n : ℝ) + (↑n : ℝ)) + 2 * ((↑n : ℝ) + 1) := by rw [hihR']
            _ = ((↑n : ℝ) + 2) * ((↑n : ℝ) + 1) := by ring
        exact_mod_cast hR
  have hc : ((n + 1).choose 2 : ℝ) * 2 = (n + 1 : ℝ) * (n : ℝ) := by
    have h' : ((n + 1).choose 2 : ℝ) * 2 = 2 * ((n + 1).choose 2 : ℝ) := by ring
    rw [h']
    exact_mod_cast h2m
  rw [show ((n + 1 : ℝ) * (n : ℝ)) / 2 = ((n + 1).choose 2 : ℝ) by
    rw [hc.symm]
    field_simp]

/-- `1 + top = 3m/(2m-t)`, where `t = tVal m`. -/
private lemma topVal_one_add (m : ℕ) (hm : 4 ≤ m) :
    1 + topVal m = 3 * (m : ℝ) / (2 * (m : ℝ) - (tVal m : ℝ)) := by
  have htwo : 2 * (tVal m : ℝ) ≤ (m : ℝ) := by exact_mod_cast tVal_two_le m
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden_pos : 0 < 2 * (m : ℝ) - (tVal m : ℝ) := by nlinarith [htwo, hm_pos]
  have hden_ne : 2 * (m : ℝ) - (tVal m : ℝ) ≠ 0 := hden_pos.ne'
  dsimp [topVal]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hmain : 1 + ((m : ℝ) + (tVal m : ℝ)) * (2 * (m : ℝ) - (tVal m : ℝ))⁻¹ =
      3 * (m : ℝ) * (2 * (m : ℝ) - (tVal m : ℝ))⁻¹ := by
    rw [show (1 : ℝ) = (2 * (m : ℝ) - (tVal m : ℝ)) * (2 * (m : ℝ) - (tVal m : ℝ))⁻¹ by
      rw [mul_inv_cancel₀ hden_ne]]
    ring
  exact hmain

/-- `c(top) = 1 - 3/(2m-t)`, where `t = tVal m`. -/
private lemma cVal_top (m : ℕ) (hm : 4 ≤ m) :
    cVal m (topVal m) = 1 - 3 / (2 * (m : ℝ) - (tVal m : ℝ)) := by
  have htwo : 2 * (tVal m : ℝ) ≤ (m : ℝ) := by exact_mod_cast tVal_two_le m
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden_pos : 0 < 2 * (m : ℝ) - (tVal m : ℝ) := by nlinarith [htwo, hm_pos]
  have hden_ne : 2 * (m : ℝ) - (tVal m : ℝ) ≠ 0 := hden_pos.ne'
  have hden_ne2 : (tVal m : ℝ) - 2 * (m : ℝ) ≠ 0 := by nlinarith
  have hden_ne3 : (m : ℝ) * 2 - (tVal m : ℝ) ≠ 0 := by nlinarith
  dsimp [cVal, topVal]
  field_simp [hden_ne, hden_ne2, hden_ne3, hm_pos.ne']
  ring

/-- `f_{i+1}(top) = (1 - 3/(2m-t))^(i+1)`, where `t = tVal m`. -/
private lemma fVal_top (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    fVal m (topVal m) (i + 1) =
      (1 - 3 / (2 * (m : ℝ) - (tVal m : ℝ))) ^ (i + 1) := by
  dsimp [fVal]
  rw [cVal_top m hm]

/-- The algebraic core of Lemma 2.2: for `1 <= i <= t`,
    `(2m-t)(3i+6) - 2(3m^2-6mt) > 9i(i+1)`. -/
private lemma core_ineq {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    9 * (i : ℝ) * ((i : ℝ) + 1) <
      (2 * (m : ℝ) - (tVal m : ℝ)) * (3 * (i : ℝ) + 6) -
        2 * (3 * (m : ℝ) ^ 2 - 6 * (m : ℝ) * (tVal m : ℝ)) := by
  have hi_le_t : (i : ℝ) ≤ (tVal m : ℝ) := by exact_mod_cast hi_le
  have hi_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  rcases Nat.even_or_odd m with hpar | hodd
  · rcases hpar with ⟨r, rfl⟩
    have ht : (tVal (r + r) : ℝ) = (r : ℝ) := by
      have h : tVal (r + r) = r := by dsimp [tVal]; omega
      exact_mod_cast h
    rw [ht]
    push_cast
    nlinarith [hi_le_t, hi_pos]
  · rcases hodd with ⟨r, rfl⟩
    have ht : (tVal (2 * r + 1) : ℝ) = (r : ℝ) := by
      have h : tVal (2 * r + 1) = r := by dsimp [tVal]; omega
      exact_mod_cast h
    rw [ht]
    push_cast
    nlinarith [hi_le_t, hi_pos]

/-- At `x = (m+t)/(2m-t)` we have `1/2 <= g_i` (second half of Lemma 2.2). -/
lemma gVal_upper_top {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    1 / 2 < gVal m (topVal m) i := by
  let d : ℝ := 2 * (m : ℝ) - (tVal m : ℝ)
  have htwo : 2 * (tVal m : ℝ) ≤ (m : ℝ) := by exact_mod_cast tVal_two_le m
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < d := by
    dsimp [d]
    nlinarith [htwo, hm_pos]
  have hden_ne : d ≠ 0 := ne_of_gt hden_pos
  have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi
  have hi_ne : (i : ℝ) ≠ 0 := ne_of_gt hi_pos
  have htop_nonneg : 0 ≤ topVal m := le_trans (by norm_num) (five_seven_le_top hm)
  have htop1 : 1 + topVal m ≠ 0 := by nlinarith [htop_nonneg]
  have hg := gVal_closed m (by omega) (topVal m) i (by omega) htop1
  have hg2 : gVal m (topVal m) i =
      d / (3 * (i : ℝ)) * (topVal m ^ 2 - fVal m (topVal m) (i + 1)) := by
    rw [hg]
    have h1 : 1 + topVal m = 3 * (m : ℝ) / d := by
      dsimp [d]
      rw [topVal_one_add m hm]
    have hmul : (m : ℝ) / ((1 + topVal m) * (i : ℝ)) = d / (3 * (i : ℝ)) := by
      rw [h1]
      field_simp [hden_ne, hi_ne]
    rw [hmul]
  have hf : fVal m (topVal m) (i + 1) = (1 - 3 / d) ^ (i + 1) := by
    dsimp [d]
    rw [fVal_top m hm i]
  have hA : topVal m ^ 2 = ((m : ℝ) + (tVal m : ℝ)) ^ 2 / d ^ 2 := by
    dsimp [topVal, d]
    rw [div_pow]
  have hx0 : 0 ≤ 3 / d := div_nonneg (by norm_num) (le_of_lt hden_pos)
  have hx1 : 3 / d ≤ 1 := (div_le_one₀ hden_pos).2 (by nlinarith [htwo, hmr])
  have hbern := bernoulli_quadratic (n := i + 1) (x := 3 / d) hx0 hx1
  have hcore := core_ineq hm i hi hi_le
  have hstep : 1 - ((i + 1 : ℕ) : ℝ) * (3 / d) + ((i + 1).choose 2 : ℝ) * (3 / d) ^ 2
      < topVal m ^ 2 - 3 * (i : ℝ) / (2 * d) := by
    rw [hA]
    rw [choose_two_succ i]
    field_simp [hden_ne]
    have hid : 2 * ((m : ℝ) + (tVal m : ℝ)) ^ 2 - 2 * d ^ 2 =
        -6 * (m : ℝ) ^ 2 + 12 * (m : ℝ) * (tVal m : ℝ) := by
      dsimp [d]
      ring
    dsimp [d] at *
    push_cast
    nlinarith [hcore, hid]
  have hw : (1 - 3 / d) ^ (i + 1) < topVal m ^ 2 - 3 * (i : ℝ) / (2 * d) :=
    lt_of_le_of_lt hbern hstep
  have hmain : 3 * (i : ℝ) / (2 * d) < topVal m ^ 2 - (1 - 3 / d) ^ (i + 1) := by
    nlinarith [hw]
  have hgoal : 1 / 2 < d / (3 * (i : ℝ)) * (topVal m ^ 2 - (1 - 3 / d) ^ (i + 1)) := by
    have hfactor_pos : 0 < d / (3 * (i : ℝ)) := by
      exact div_pos hden_pos (by nlinarith [hi_pos])
    have hmul_le := mul_lt_mul_of_pos_right hmain hfactor_pos
    have hmul_eq : (3 * (i : ℝ) / (2 * d)) * (d / (3 * (i : ℝ))) = 1 / 2 := by
      field_simp [hden_ne, hi_ne]
    rw [hmul_eq] at hmul_le
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le
  simpa [hg2, hf] using hgoal

/-- Lemma 2.2: `g_i(x) = 1/2` has a root in `[5/7, (m+t)/(2m-t)]`
    for `1 <= i <= t`. -/
lemma exists_root_gVal_eq_half {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    ∃ x ∈ Set.Icc (5 / 7 : ℝ) (topVal m), gVal m x i = 1 / 2 := by
  have h5top : (5 / 7 : ℝ) ≤ topVal m := five_seven_le_top hm
  have htop1 : topVal m ≤ 1 := topVal_le_one hm
  have hsub : Set.Icc (5 / 7 : ℝ) (topVal m) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨le_trans (by norm_num) hz.1, le_trans hz.2 htop1⟩
  have hcont : ContinuousOn (fun x : ℝ => gVal m x i)
      (Set.Icc (5 / 7 : ℝ) (topVal m)) := by
    exact (gVal_continuousOn m i (by omega)).mono hsub
  have himage := isPreconnected_Icc.intermediate_value (a := (5 / 7 : ℝ)) (b := topVal m)
    (by simp [h5top]) (by simp [h5top]) hcont
  have hhalf : 1 / 2 ∈ Set.Icc (gVal m (5 / 7 : ℝ) i) (gVal m (topVal m) i) :=
    ⟨gVal_lower_5_7 hm i hi (by simpa [tVal] using hi_le),
     le_of_lt (gVal_upper_top hm i hi hi_le)⟩
  rcases himage hhalf with ⟨x, hxmem, hxeq⟩
  exact ⟨x, hxmem, hxeq⟩

/-- Lemma 2.2: the root is unique (strict monotonicity of `g_i`). -/
lemma exists_unique_root_gVal_eq_half {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i)
    (hi_le : i ≤ tVal m) :
    ∃! x ∈ Set.Icc (5 / 7 : ℝ) (topVal m), gVal m x i = 1 / 2 := by
  rcases exists_root_gVal_eq_half hm i hi hi_le with ⟨x, hxmem, hxeq⟩
  refine ⟨x, ⟨hxmem, hxeq⟩, ?_⟩
  intro y hymem
  rcases hymem with ⟨hymem, hyeq⟩
  have hmono : StrictMonoOn (fun x : ℝ => gVal m x i) (Set.Icc (0 : ℝ) 1) :=
    gVal_strictMonoOn hm i hi (by simpa [tVal] using hi_le)
  have hsub : Set.Icc (5 / 7 : ℝ) (topVal m) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨le_trans (by norm_num) hz.1, le_trans hz.2 (topVal_le_one hm)⟩
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := hsub hxmem
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := hsub hymem
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hlt := hmono hy01 hx01 hxy
    nlinarith [hxeq, hyeq, hlt]
  · have hlt := hmono hx01 hy01 hyx
    nlinarith [hxeq, hyeq, hlt]

/-- The unique root `x_i^(m)` of `g_i = 1/2` in `[5/7, (m+t)/(2m-t)]`. -/
noncomputable def xRoot (m i : ℕ) (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) : ℝ :=
  Classical.choose (exists_unique_root_gVal_eq_half (m := m) hm i hi hi_le)

/-- `xRoot` lies in `[5/7, (m+t)/(2m-t)]`. -/
lemma xRoot_mem (m i : ℕ) (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    xRoot m i hm hi hi_le ∈ Set.Icc (5 / 7 : ℝ) (topVal m) :=
  (Classical.choose_spec (exists_unique_root_gVal_eq_half (m := m) hm i hi hi_le)).1.1

/-- `g_i(xRoot) = 1/2`. -/
lemma xRoot_eq (m i : ℕ) (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    gVal m (xRoot m i hm hi hi_le) i = 1 / 2 :=
  (Classical.choose_spec (exists_unique_root_gVal_eq_half (m := m) hm i hi hi_le)).1.2

/-- `xRoot` is the unique root in the interval. -/
lemma xRoot_unique (m i : ℕ) (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m)
    {x : ℝ} (hxmem : x ∈ Set.Icc (5 / 7 : ℝ) (topVal m)) (hxeq : gVal m x i = 1 / 2) :
    x = xRoot m i hm hi hi_le :=
  (Classical.choose_spec (exists_unique_root_gVal_eq_half (m := m) hm i hi hi_le)).2 x
    ⟨hxmem, hxeq⟩

/-- `xRoot` lies in the unit interval `[0,1]`. -/
lemma xRoot_mem_unit {m i : ℕ} (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m) :
    xRoot m i hm hi hi_le ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_trans (by norm_num) (xRoot_mem m i hm hi hi_le).1,
   le_trans (xRoot_mem m i hm hi hi_le).2 (topVal_le_one hm)⟩

/-! ### Lemma 2.3: monotonicity of the endpoint values -/

/-- Lemma 2.3: if `f_{i+1}(x_i) >= 1/2` then `f_{i+1}(x_{i+1}) >= 1/2`. -/
lemma fVal_succ_ge_of_ge {m i : ℕ} (hm : 4 ≤ m) (hi : 1 ≤ i) (hi_le : i ≤ tVal m)
    (hi1 : i + 1 ≤ tVal m) (h : 1 / 2 ≤ fVal m (xRoot m i hm hi hi_le) (i + 1)) :
    1 / 2 ≤ fVal m (xRoot m (i + 1) hm (by omega) hi1) (i + 1) := by
  by_contra hnot
  have hlt' : fVal m (xRoot m (i + 1) hm (by omega) hi1) (i + 1) < 1 / 2 := by
    nlinarith
  have hmem : xRoot m i hm hi hi_le ∈ Set.Icc (0 : ℝ) 1 := xRoot_mem_unit hm hi hi_le
  have hmem1 : xRoot m (i + 1) hm (by omega) hi1 ∈ Set.Icc (0 : ℝ) 1 :=
    xRoot_mem_unit hm (by omega) hi1
  have hxeq1 : gVal m (xRoot m (i + 1) hm (by omega) hi1) (i + 1) = 1 / 2 :=
    xRoot_eq m (i + 1) hm (by omega) hi1
  have hrec1 := gVal_rec m (xRoot m (i + 1) hm (by omega) hi1) i (by omega)
  push_cast at hrec1
  have hgi1 : 1 / 2 < gVal m (xRoot m (i + 1) hm (by omega) hi1) i := by
    nlinarith [hrec1, hlt', hxeq1, (by exact_mod_cast hi : (0 : ℝ) < (i : ℝ))]
  have hmono_i : MonotoneOn (fun x : ℝ => gVal m x i) (Set.Icc (0 : ℝ) 1) :=
    (gVal_strictMonoOn hm i hi (by simpa [tVal] using hi_le)).monotoneOn
  have hxeq : gVal m (xRoot m i hm hi hi_le) i = 1 / 2 := xRoot_eq m i hm hi hi_le
  have hxlt : xRoot m i hm hi hi_le < xRoot m (i + 1) hm (by omega) hi1 := by
    by_contra hnot2
    have hle : xRoot m (i + 1) hm (by omega) hi1 ≤ xRoot m i hm hi hi_le := le_of_not_gt hnot2
    have hle' : gVal m (xRoot m (i + 1) hm (by omega) hi1) i ≤
        gVal m (xRoot m i hm hi hi_le) i := hmono_i hmem1 hmem hle
    nlinarith [hgi1, hle', hxeq]
  have hmono_i1 : StrictMonoOn (fun x : ℝ => gVal m x (i + 1)) (Set.Icc (0 : ℝ) 1) :=
    gVal_strictMonoOn hm (i + 1) (by omega) (by simpa [tVal] using hi1)
  have hgi1_lt : gVal m (xRoot m i hm hi hi_le) (i + 1) < 1 / 2 := by
    have hlt2 := hmono_i1 hmem hmem1 hxlt
    nlinarith [hlt2, hxeq1]
  have hrec := gVal_rec m (xRoot m i hm hi hi_le) i (by omega)
  push_cast at hrec
  have hf_lt : fVal m (xRoot m i hm hi hi_le) (i + 1) < 1 / 2 := by
    nlinarith [hrec, hgi1_lt, hxeq, (by exact_mod_cast hi : (0 : ℝ) < (i : ℝ))]
  nlinarith [h, hf_lt]

/-! ### Lemma 2.4: `f_{t+1}(x_t) <= 1/2` -/

/-- Lemma 2.4: `f_{t+1}(x_t) <= 1/2`. -/
lemma fVal_t_succ_le {m : ℕ} (hm : 4 ≤ m) :
    fVal m (xRoot m (tVal m) hm (by dsimp [tVal]; omega) (by rfl)) (tVal m + 1) ≤ 1 / 2 := by
  let t : ℕ := tVal m
  have ht1 : 1 ≤ t := by dsimp [t, tVal]; omega
  have htle : t ≤ tVal m := by dsimp [t]; rfl
  have htpos : (t : ℝ) ≠ 0 := by exact_mod_cast (by dsimp [t, tVal]; omega : t ≠ 0)
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have htwo_le : 2 * (t : ℝ) ≤ (m : ℝ) := by
    dsimp [t]
    exact_mod_cast tVal_two_le m
  let hx : ℝ := xRoot m t hm ht1 htle
  have hxmem : hx ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [hx]
    exact xRoot_mem_unit hm ht1 htle
  have hxeq : gVal m hx t = 1 / 2 := by
    dsimp [hx]
    exact xRoot_eq m t hm ht1 htle
  have htop_mem : topVal m ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans (by norm_num) (five_seven_le_top hm), topVal_le_one hm⟩
  have hgtop : 1 / 2 < gVal m (topVal m) t :=
    gVal_upper_top hm t ht1 htle
  have hmono : MonotoneOn (fun x : ℝ => gVal m x t) (Set.Icc (0 : ℝ) 1) :=
    (gVal_strictMonoOn hm t ht1 (by dsimp [t]; rfl)).monotoneOn
  have hxlt : hx < topVal m := by
    by_contra hnot
    have hle : topVal m ≤ hx := le_of_not_gt hnot
    have hle' : gVal m (topVal m) t ≤ gVal m hx t := hmono htop_mem hxmem hle
    nlinarith [hgtop, hle', hxeq]
  have hx1 : hx < 1 := lt_of_lt_of_le hxlt (topVal_le_one hm)
  have hxpos : 0 < hx := by
    have h := (xRoot_mem m t hm ht1 htle).1
    dsimp [hx]
    nlinarith
  have htop_nonneg : 0 ≤ topVal m := le_trans (by norm_num) (five_seven_le_top hm)
  have htop1 : 1 + hx ≠ 0 := by
    have : 0 ≤ hx := le_of_lt hxpos
    nlinarith
  have hclosed := gVal_closed m (by omega) hx t (by dsimp [t, tVal]; omega) htop1
  have hmain : 2 * (m : ℝ) * (hx ^ 2 - fVal m hx (t + 1)) = (t : ℝ) * (1 + hx) := by
    have hmul : (m : ℝ) / ((1 + hx) * (t : ℝ)) * (hx ^ 2 - fVal m hx (t + 1)) = 1 / 2 := by
      rw [← hclosed]
      exact hxeq
    field_simp [htop1, htpos, hm_pos.ne'] at hmul
    nlinarith [hmul]
  have hx2 : hx ^ 2 < hx := by nlinarith [hxpos, hx1]
  have hfirst : 2 * (m : ℝ) * hx ^ 2 < 2 * (m : ℝ) * hx := by
    exact mul_lt_mul_of_pos_left hx2 (by nlinarith [hm_pos])
  have hden_pos : 0 < 2 * (m : ℝ) - (t : ℝ) := by
    nlinarith [htwo_le, hm_pos]
  have hsecond : (2 * (m : ℝ) - (t : ℝ)) * hx < (m : ℝ) + (t : ℝ) := by
    have hlt3 : hx < ((m : ℝ) + (t : ℝ)) / (2 * (m : ℝ) - (t : ℝ)) := by
      change hx < topVal m
      exact hxlt
    simpa [mul_comm] using (lt_div_iff₀ hden_pos).mp hlt3
  have hmm : 2 * (m : ℝ) * hx ^ 2 - (t : ℝ) * (1 + hx) < (m : ℝ) := by
    nlinarith [hfirst, hsecond]
  have hf_lt : fVal m hx (t + 1) < 1 / 2 := by
    have htwo : 2 * (m : ℝ) * fVal m hx (t + 1) < (m : ℝ) := by
      nlinarith [hmm, hmain]
    have htwo_pos : 0 < 2 * (m : ℝ) := by nlinarith [hm_pos]
    nlinarith [htwo, htwo_pos]
  dsimp [hx, t] at hf_lt
  exact le_of_lt hf_lt

/-! ### Lemma 2.5: `I^(m) != empty`, and `q_m, beta_m, gamma_m` -/

/-- `x_1^(m)` lies in `[0,1]`. -/
lemma x1Val_mem_unit {m : ℕ} (hm : 4 ≤ m) : x1Val m ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [x1Val]
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) ^ 2 - 2 := by nlinarith [hmr]
  constructor
  · have hnum : 0 ≤ 2 * (m : ℝ) ^ 2 - 3 * (m : ℝ) + 2 := by nlinarith [hmr]
    exact div_nonneg hnum (le_of_lt hden)
  · exact (div_le_one₀ hden).2 (by nlinarith [hmr])

/-- `g_1(x_1^(m)) = 1/2`. -/
lemma gVal_one_x1_val {m : ℕ} (hm : 4 ≤ m) : gVal m (x1Val m) 1 = 1 / 2 := by
  exact (gVal_one_eq_half m (by omega) (by omega) (x1Val m)).2 rfl

/-- `xRoot m 1 = x_1^(m)` (both are the unique root of `g_1 = 1/2`). -/
lemma xRoot_one_eq (m : ℕ) (hm : 4 ≤ m) (hi : 1 ≤ 1) (hi_le : 1 ≤ tVal m) :
    xRoot m 1 hm hi hi_le = x1Val m := by
  have hx1_unit : x1Val m ∈ Set.Icc (0 : ℝ) 1 := x1Val_mem_unit hm
  have hxr_unit : xRoot m 1 hm hi hi_le ∈ Set.Icc (0 : ℝ) 1 := xRoot_mem_unit hm hi hi_le
  have hx1eq : gVal m (x1Val m) 1 = 1 / 2 := gVal_one_x1_val hm
  have hxreq : gVal m (xRoot m 1 hm hi hi_le) 1 = 1 / 2 := xRoot_eq m 1 hm hi hi_le
  have hmono : StrictMonoOn (fun x : ℝ => gVal m x 1) (Set.Icc (0 : ℝ) 1) :=
    gVal_strictMonoOn hm 1 (by omega) (by simpa [tVal] using hi_le)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hlt := hmono hxr_unit hx1_unit hxy
    nlinarith [hlt, hxreq, hx1eq]
  · have hlt := hmono hx1_unit hxr_unit hyx
    nlinarith [hlt, hxreq, hx1eq]

/-- `f_1(x_1^(m)) > 1/2` for `m >= 4` (paper (8)). -/
lemma fVal_one_x1_gt {m : ℕ} (hm : 4 ≤ m) : 1 / 2 < fVal m (x1Val m) 1 := by
  have h := fVal_one_x1 m (by omega) (by omega)
  rw [h]
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 2 * ((m : ℝ) ^ 2 - 1) := by nlinarith [hmr]
  have hdenm1 : (m : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [hmr]
  have hnum : 2 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 1 > (m : ℝ) ^ 2 - 1 := by nlinarith [hmr]
  exact (lt_div_iff₀ hden).2 (by nlinarith [hnum])

/-- The set `I^(m) = {i | f_{i+1}(x_i) <= 1/2 <= f_i(x_i)}`. -/
def IsetAt (m i : ℕ) (hm : 4 ≤ m) : Prop :=
  ∃ (hi : 1 ≤ i) (hi_le : i ≤ tVal m),
    fVal m (xRoot m i hm hi hi_le) (i + 1) ≤ 1 / 2 ∧
    1 / 2 ≤ fVal m (xRoot m i hm hi hi_le) i

/-- Lemma 2.5: assuming `I^(m) = empty`, all `f_i(x_i) >= 1/2` for `1 <= i <= t`. -/
lemma fVal_self_ge_half {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ tVal m)
    (hI : ∀ k : ℕ, IsetAt m k hm → False) :
    1 / 2 ≤ fVal m (xRoot m i hm hi hi_le) i := by
  revert hi hi_le
  induction i with
  | zero =>
      intro hi hi_le
      omega
  | succ n ih =>
      intro hi hi_le
      by_cases hn : n = 0
      · subst n
        have hxr : xRoot m 1 hm hi hi_le = x1Val m := xRoot_one_eq m hm hi hi_le
        norm_num
        simpa [hxr] using (le_of_lt (fVal_one_x1_gt hm))
      · have hn1 : 1 ≤ n := by omega
        have hn_le : n ≤ tVal m := by omega
        have hih := ih hn1 hn_le
        have hf_gt : 1 / 2 < fVal m (xRoot m n hm hn1 hn_le) (n + 1) := by
          by_contra hnot
          have hle1 : fVal m (xRoot m n hm hn1 hn_le) (n + 1) ≤ 1 / 2 := le_of_not_gt hnot
          exact hI n ⟨hn1, hn_le, hle1, hih⟩
        exact fVal_succ_ge_of_ge hm hn1 hn_le hi_le (le_of_lt hf_gt)

/-- Lemma 2.5: `I^(m) != empty`. -/
lemma IsetAt_nonempty (m : ℕ) (hm : 4 ≤ m) : ∃ i : ℕ, IsetAt m i hm := by
  by_contra hnone
  push Not at hnone
  have ht1 : 1 ≤ tVal m := by dsimp [tVal]; omega
  have htl : 1 / 2 ≤ fVal m (xRoot m (tVal m) hm ht1 (by rfl)) (tVal m) :=
    fVal_self_ge_half hm (tVal m) ht1 (by rfl) hnone
  have hf_gt : 1 / 2 < fVal m (xRoot m (tVal m) hm ht1 (by rfl)) (tVal m + 1) := by
    by_contra hnot
    have hle1 : fVal m (xRoot m (tVal m) hm ht1 (by rfl)) (tVal m + 1) ≤ 1 / 2 :=
      le_of_not_gt hnot
    exact hnone (tVal m) ⟨ht1, by rfl, hle1, htl⟩
  have hf_le : fVal m (xRoot m (tVal m) hm ht1 (by rfl)) (tVal m + 1) ≤ 1 / 2 :=
    fVal_t_succ_le hm
  nlinarith [hf_gt, hf_le]

/-- `q_m = min I^(m)`, the least index in `IsetAt` (paper Lemma 2.5). -/
noncomputable def qVal (m : ℕ) (hm : 4 ≤ m) : ℕ := by
  classical
  exact Nat.find (IsetAt_nonempty m hm)

/-- `q_m` belongs to `I^(m)`. -/
lemma qVal_mem (m : ℕ) (hm : 4 ≤ m) : IsetAt m (qVal m hm) hm := by
  classical
  exact Nat.find_spec (IsetAt_nonempty m hm)

/-- `q_m` is the least index in `I^(m)`. -/
lemma qVal_min (m : ℕ) (hm : 4 ≤ m) {k : ℕ} (hk : IsetAt m k hm) : qVal m hm ≤ k := by
  classical
  exact Nat.find_min' (IsetAt_nonempty m hm) hk

/-- `1 <= q_m`. -/
lemma qVal_ge_one (m : ℕ) (hm : 4 ≤ m) : 1 ≤ qVal m hm := (qVal_mem m hm).1

/-- `q_m <= t`. -/
lemma qVal_le_t (m : ℕ) (hm : 4 ≤ m) : qVal m hm ≤ tVal m := (qVal_mem m hm).2.1

/-- `beta_m = x_{q_m}`. -/
noncomputable def betaVal (m : ℕ) (hm : 4 ≤ m) : ℝ :=
  xRoot m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)

/-- `gamma_m = min(beta_m, alpha)`. -/
noncomputable def gammaVal (m : ℕ) (hm : 4 ≤ m) : ℝ :=
  min (betaVal m hm) tanAlpha

/-! ### Lemma 2.6: properties of `gamma_m` -/

/-- `alpha(alpha - 1/2) = 1/3`. -/
lemma tanAlpha_sq : tanAlpha * (tanAlpha - 1 / 2) = 1 / 3 := by
  dsimp [tanAlpha]
  have hsq : Real.sqrt 57 * Real.sqrt 57 = 57 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : 0 ≤ (57 : ℝ))
  nlinarith [hsq]

/-- `alpha` is positive. -/
lemma tanAlpha_pos : 0 < tanAlpha := by
  dsimp [tanAlpha]
  have hnn : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg 57
  nlinarith

/-- `5/7 <= alpha`. -/
lemma tanAlpha_ge_five_seven : (5 / 7 : ℝ) ≤ tanAlpha := by
  dsimp [tanAlpha]
  have hsq : Real.sqrt 57 * Real.sqrt 57 = 57 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : 0 ≤ (57 : ℝ))
  have hnn : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg 57
  have hsqr : (7 * Real.sqrt 57) ^ 2 ≥ 39 ^ 2 := by
    rw [sq, sq]
    nlinarith [hsq]
  nlinarith [hsqr, hnn]

/-- `alpha < 1`. -/
lemma tanAlpha_lt_one : tanAlpha < 1 := by
  dsimp [tanAlpha]
  have hsq : Real.sqrt 57 * Real.sqrt 57 = 57 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : 0 ≤ (57 : ℝ))
  have hnn : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg 57
  nlinarith [hsq, hnn]

/-- `gamma_m <= beta_m`. -/
lemma gammaVal_le_beta (m : ℕ) (hm : 4 ≤ m) : gammaVal m hm ≤ betaVal m hm := by
  dsimp [gammaVal]
  exact min_le_left _ _

/-- `gamma_m <= alpha`. -/
lemma gammaVal_le_alpha (m : ℕ) (hm : 4 ≤ m) : gammaVal m hm ≤ tanAlpha := by
  dsimp [gammaVal]
  exact min_le_right _ _

/-- `5/7 <= gamma_m`. -/
lemma gammaVal_ge_five_seven (m : ℕ) (hm : 4 ≤ m) : (5 / 7 : ℝ) ≤ gammaVal m hm := by
  dsimp [gammaVal]
  exact le_min
    (le_trans (by norm_num)
      (xRoot_mem m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)).1)
    (tanAlpha_ge_five_seven)

/-- `gamma_m <= 1`. -/
lemma gammaVal_le_one (m : ℕ) (hm : 4 ≤ m) : gammaVal m hm ≤ 1 := by
  have hb : betaVal m hm ≤ 1 :=
    le_trans (xRoot_mem m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)).2
      (topVal_le_one hm)
  exact le_trans (gammaVal_le_beta m hm) hb

/-- `11/15 <= alpha`. -/
lemma tanAlpha_ge_eleven_fifteen : (11 / 15 : ℝ) ≤ tanAlpha := by
  dsimp [tanAlpha]
  have hsq : Real.sqrt 57 * Real.sqrt 57 = 57 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : 0 ≤ (57 : ℝ))
  have hnn : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg 57
  have hsqr : (5 * Real.sqrt 57) ^ 2 ≥ 29 ^ 2 := by
    rw [sq, sq]
    nlinarith [hsq]
  nlinarith [hsqr, hnn]

/-- `37/48 <= alpha`. -/
lemma tanAlpha_ge_thirty_seven_forty_eight : (37 / 48 : ℝ) ≤ tanAlpha := by
  dsimp [tanAlpha]
  have hsq : Real.sqrt 57 * Real.sqrt 57 = 57 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : 0 ≤ (57 : ℝ))
  have hnn : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg 57
  have hsqr : (4 * Real.sqrt 57) ^ 2 ≥ 25 ^ 2 := by
    rw [sq, sq]
    nlinarith [hsq]
  nlinarith [hsqr, hnn]

/-- For `4 <= m <= 6` we have `1 in I^(m)`, so `q_m = 1`. -/
lemma IsetAt_one_of_le_six {m : ℕ} (hm : 4 ≤ m) (hm6 : m ≤ 6) : IsetAt m 1 hm := by
  have h1le : 1 ≤ 1 := le_rfl
  have h1t : 1 ≤ tVal m := by
    dsimp [tVal]
    omega
  refine ⟨h1le, h1t, ?_⟩
  have hxr : xRoot m 1 hm h1le h1t = x1Val m := xRoot_one_eq m hm h1le h1t
  constructor
  · -- f_2(x_1) <= 1/2
    have hf1 := fVal_one_x1 m (by omega) (by omega)
    have hsq : fVal m (x1Val m) 1 * fVal m (x1Val m) 1 ≤ 1 / 2 := by
      rw [hf1]
      interval_cases m <;> norm_num
    have hf2 : fVal m (x1Val m) 2 = fVal m (x1Val m) 1 * fVal m (x1Val m) 1 := by
      dsimp [fVal]
      rw [pow_succ]
      simp [pow_one]
    rw [hxr]
    rw [hf2]
    exact hsq
  · -- 1/2 <= f_1(x_1)
    rw [hxr]
    exact le_of_lt (fVal_one_x1_gt hm)

/-- For `4 <= m <= 6`, `q_m = 1`. -/
lemma qVal_eq_one_of_le_six {m : ℕ} (hm : 4 ≤ m) (hm6 : m ≤ 6) : qVal m hm = 1 := by
  have h1 : IsetAt m 1 hm := IsetAt_one_of_le_six hm hm6
  have hle : qVal m hm ≤ 1 := qVal_min m hm h1
  have hge : 1 ≤ qVal m hm := qVal_ge_one m hm
  omega

/-- Lemma 2.6(i): the chain of `f`-values around `gamma_m`. -/
lemma fVal_gamma_chain (m : ℕ) (hm : 4 ≤ m) :
    fVal m (betaVal m hm) (qVal m hm + 1) ≤ 1 / 2 ∧
    1 / 2 ≤ fVal m (gammaVal m hm) (qVal m hm) ∧
    (∀ j : ℕ, 1 ≤ j → j < qVal m hm →
      fVal m (gammaVal m hm) (j + 1) ≤ fVal m (gammaVal m hm) j) ∧
    fVal m (gammaVal m hm) (qVal m hm) ≤ 1 := by
  have hqmem := qVal_mem m hm
  rcases hqmem with ⟨hq1, hqt, hfq1, hfq2⟩
  have hc_pos : 0 < cVal m (gammaVal m hm) := by
    dsimp [cVal]
    have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg1 : gammaVal m hm < 1 :=
      lt_of_le_of_lt (gammaVal_le_alpha m hm) (tanAlpha_lt_one)
    have hnum : 0 < (m : ℝ) - 1 - gammaVal m hm := by
      have h3 : (3 : ℝ) - gammaVal m hm > 2 := by nlinarith [hg1]
      have h4 : (m : ℝ) - 1 - gammaVal m hm ≥ (3 : ℝ) - gammaVal m hm := by
        nlinarith [hmr]
      nlinarith
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    exact div_pos hnum hm_pos
  have hc_le_one : cVal m (gammaVal m hm) ≤ 1 := by
    dsimp [cVal]
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hnum : (m : ℝ) - 1 - gammaVal m hm ≤ (m : ℝ) := by
      have hg_nonneg : 0 ≤ gammaVal m hm :=
        le_trans (by norm_num) (gammaVal_ge_five_seven m hm)
      nlinarith [hg_nonneg]
    exact (div_le_one₀ hm_pos).2 hnum
  constructor
  · dsimp [betaVal]
    exact hfq1
  constructor
  · have hgamma_le : gammaVal m hm ≤ betaVal m hm := gammaVal_le_beta m hm
    have hanti : AntitoneOn (fun x : ℝ => fVal m x (qVal m hm)) (Set.Icc (0 : ℝ) 1) :=
      (fVal_strictAntiOn (m := m) (by omega) (qVal m hm) (by omega)).antitoneOn
    have hg01 : gammaVal m hm ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (by norm_num) (gammaVal_ge_five_seven m hm), gammaVal_le_one m hm⟩
    have hb01 : betaVal m hm ∈ Set.Icc (0 : ℝ) 1 :=
      xRoot_mem_unit hm (qVal_ge_one m hm) (qVal_le_t m hm)
    have hle' : fVal m (gammaVal m hm) (qVal m hm) ≥ fVal m (betaVal m hm) (qVal m hm) :=
      hanti hg01 hb01 hgamma_le
    have hbq : fVal m (betaVal m hm) (qVal m hm) =
        fVal m (xRoot m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)) (qVal m hm) := by
      rfl
    nlinarith [hle', hfq2, hbq]
  constructor
  · intro j hj1 hjlt
    dsimp [fVal]
    rw [pow_succ]
    have hpow_nonneg : 0 ≤ cVal m (gammaVal m hm) ^ j :=
      pow_nonneg (le_of_lt hc_pos) j
    exact mul_le_of_le_one_right hpow_nonneg hc_le_one
  · dsimp [fVal]
    exact pow_le_one₀ (le_of_lt hc_pos) hc_le_one

/-- Lemma 2.6(ii): `gamma_m (gamma_m - 1/2) <= 1/3`. -/
lemma gammaVal_mul_le_one_third (m : ℕ) (hm : 4 ≤ m) :
    gammaVal m hm * (gammaVal m hm - 1 / 2) ≤ 1 / 3 := by
  have hg_le_a : gammaVal m hm ≤ tanAlpha := gammaVal_le_alpha m hm
  have hg_ge : (5 / 7 : ℝ) ≤ gammaVal m hm := gammaVal_ge_five_seven m hm
  have hfact : (gammaVal m hm - tanAlpha) * (gammaVal m hm + tanAlpha - 1 / 2) ≤ 0 := by
    have h1 : gammaVal m hm - tanAlpha ≤ 0 := by nlinarith [hg_le_a]
    have h2 : 0 ≤ gammaVal m hm + tanAlpha - 1 / 2 := by
      nlinarith [hg_ge, tanAlpha_ge_five_seven]
    nlinarith
  nlinarith [hfact, tanAlpha_sq]

/-- Lemma 2.6(ii): `gamma_m (gamma_m - 1/2) <= 1/2 - 1/m`. -/
lemma gammaVal_mul_le_one_half_sub (m : ℕ) (hm : 4 ≤ m) :
    gammaVal m hm * (gammaVal m hm - 1 / 2) ≤ 1 / 2 - 1 / (m : ℝ) := by
  by_cases hm6 : 6 ≤ m
  · have h13 : gammaVal m hm * (gammaVal m hm - 1 / 2) ≤ 1 / 3 :=
      gammaVal_mul_le_one_third m hm
    have h23 : 1 / 3 ≤ 1 / 2 - 1 / (m : ℝ) := by
      have hmr : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm6
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      field_simp [hm_pos.ne']
      nlinarith [hmr]
    nlinarith
  · have hm45 : m = 4 ∨ m = 5 := by omega
    rcases hm45 with rfl | rfl
    · have hq : qVal 4 (by norm_num) = 1 := qVal_eq_one_of_le_six (by norm_num) (by norm_num)
      have hb : betaVal 4 (by norm_num) = 11 / 15 := by
        dsimp [betaVal]
        have hxr : xRoot 4 1 (by norm_num) (by norm_num) (by norm_num [tVal]) = x1Val 4 :=
          xRoot_one_eq 4 (by norm_num) (by norm_num) (by norm_num [tVal])
        simpa [hq, hxr, x1Val] using (show x1Val 4 = 11 / 15 by norm_num [x1Val])
      have hg : gammaVal 4 (by norm_num) = 11 / 15 := by
        dsimp [gammaVal]
        rw [hb]
        exact min_eq_left tanAlpha_ge_eleven_fifteen
      rw [hg]
      norm_num
    · have hq : qVal 5 (by norm_num) = 1 := qVal_eq_one_of_le_six (by norm_num) (by norm_num)
      have hb : betaVal 5 (by norm_num) = 37 / 48 := by
        dsimp [betaVal]
        have hxr : xRoot 5 1 (by norm_num) (by norm_num) (by norm_num [tVal]) = x1Val 5 :=
          xRoot_one_eq 5 (by norm_num) (by norm_num) (by norm_num [tVal])
        simpa [hq, hxr, x1Val] using (show x1Val 5 = 37 / 48 by norm_num [x1Val])
      have hg : gammaVal 5 (by norm_num) = 37 / 48 := by
        dsimp [gammaVal]
        rw [hb]
        exact min_eq_left tanAlpha_ge_thirty_seven_forty_eight
      rw [hg]
      norm_num

/-- Lemma 2.6(iii): the average-load bound used by the adversary. -/
lemma gammaVal_main_ineq (m : ℕ) (hm : 4 ≤ m) :
    gammaVal m hm - 1 / 2 +
      (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 +
        (∑ j ∈ Finset.Icc 1 (qVal m hm), fVal m (gammaVal m hm) j))
      ≤ ((m : ℝ) - 1) / (m : ℝ) := by
  have hqmem := qVal_mem m hm
  rcases hqmem with ⟨hq1, hqt, hfq1, hfq2⟩
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
  have hg_le : gVal m (gammaVal m hm) (qVal m hm) ≤ 1 / 2 := by
    have hmono : MonotoneOn (fun x : ℝ => gVal m x (qVal m hm)) (Set.Icc (0 : ℝ) 1) :=
      (gVal_strictMonoOn hm (qVal m hm) (by omega)
        (by simpa [tVal] using qVal_le_t m hm)).monotoneOn
    have hg01 : gammaVal m hm ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (by norm_num) (gammaVal_ge_five_seven m hm), gammaVal_le_one m hm⟩
    have hb01 : betaVal m hm ∈ Set.Icc (0 : ℝ) 1 :=
      xRoot_mem_unit hm (qVal_ge_one m hm) (qVal_le_t m hm)
    have hle := hmono hg01 hb01 (gammaVal_le_beta m hm)
    have hbq : gVal m (betaVal m hm) (qVal m hm) = 1 / 2 := by
      dsimp [betaVal]
      exact xRoot_eq m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)
    nlinarith [hle, hbq]
  have hsum := gVal_mul m (gammaVal m hm) (qVal m hm) (by omega)
  have hsum' :
      (∑ j ∈ Finset.Icc 1 (qVal m hm), fVal m (gammaVal m hm) j) =
        (qVal m hm : ℝ) * gVal m (gammaVal m hm) (qVal m hm) +
          ((m : ℝ) - 1 - (m : ℝ) * gammaVal m hm) := by
    nlinarith [hsum]
  field_simp [hm_ne]
  nlinarith [hsum', hg_le]

/-! ### Phase 4: the pseudo lower bound `LB = max(LB1, LB2, LB3)` -/

/-- The `j`-th largest job of `sigma` (1-indexed), or `0` if `j` is out of range. -/
noncomputable def jthLargest (sigma : JobSequence) (j : ℕ) : ℝ := by
  classical
  exact (sigma.mergeSort (fun a b => decide (b ≤ a))).getD (j - 1) 0

/-- `LB3(m, sigma) = max over k of the sum of the (km-k+1)-st .. (km+1)-st largest jobs
    (equation in Section 3 of the paper). -/
noncomputable def LB3 (m : ℕ) (sigma : JobSequence) : ℝ := by
  classical
  exact if h : (Finset.Icc 1 ((sigma.length - 1) / m)).Nonempty then
    (Finset.Icc 1 ((sigma.length - 1) / m)).sup' h
      (fun k => ∑ j ∈ Finset.Icc (m * k - k + 1) (m * k + 1), jthLargest sigma j)
  else 0

/-- The pseudo lower bound: max of average load, largest job and `LB3`. -/
noncomputable def PseudoLBGen (m : ℕ) (sigma : JobSequence) : ℝ :=
  max (totalLoad sigma / (m : ℝ)) (max (maxJobSize sigma) (LB3 m sigma))

/-- If `n` positions of `l` (indices `< n`) all satisfy `p`, then the filter has
    length at least `n`. -/
private lemma countP_ge_of_forall_getElem {p : ℝ → Bool} :
    ∀ (l : List ℝ) (n : ℕ), n ≤ l.length →
      (∀ i : ℕ, (hi : i < l.length) → i < n → p (l.get ⟨i, hi⟩) = true) →
      n ≤ (l.filter p).length
  | [], n, hn, h => by
      simpa using hn
  | a :: l, n, hn, h => by
      by_cases hpa : p a = true
      · have h' : ∀ i : ℕ, (hi : i < l.length) → i < n - 1 → p (l.get ⟨i, hi⟩) = true := by
          intro i hi hlt
          have hi' : i + 1 < (a :: l).length := by simp [hi]
          have hget : l.get ⟨i, hi⟩ = (a :: l).get ⟨i + 1, hi'⟩ := by
            rfl
          have hlt1 : i + 1 < n := by
            have hnpos : 0 < n := by omega
            omega
          have hh := h (i + 1) hi' hlt1
          simpa [hget] using hh
        have hih : n - 1 ≤ l.length := by
          exact (Nat.sub_le_iff_le_add (b := 1)).mpr (by simpa using hn)
        have hle := countP_ge_of_forall_getElem l (n - 1) hih h'
        simp [List.filter, hpa]
        omega
      · by_cases hn0 : n = 0
        · subst n
          simp
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          have h0 : p a = true := h 0 (by simp) (by omega)
          contradiction

/-- The `j`-th largest job is `<= x` whenever fewer than `j` jobs are larger than `x`. -/
lemma jthLargest_le_of_card_lt {sigma : JobSequence} {x : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hx : 0 ≤ x) (hcard : (sigma.filter fun p => decide (x < p)).length < j) :
    jthLargest sigma j ≤ x := by
  let s := sigma.mergeSort (fun a b => decide (b ≤ a))
  have hperm : List.Perm s sigma :=
    by
      simpa [s] using (List.mergeSort_perm sigma (fun a b => decide (b ≤ a)))
  have hcard' : (s.filter fun p => decide (x < p)).length < j := by
    have hf : List.Perm (s.filter fun p => decide (x < p))
        (sigma.filter fun p => decide (x < p)) :=
      List.Perm.filter (fun p => decide (x < p)) hperm
    have hlen : (s.filter fun p => decide (x < p)).length =
        (sigma.filter fun p => decide (x < p)).length := by
      exact List.Perm.length_eq hf
    rw [hlen]
    exact hcard
  have htrans : ∀ a b c : ℝ, decide (b ≤ a) = true → decide (c ≤ b) = true →
      decide (c ≤ a) = true := by
    intro a b c h1 h2
    rw [decide_eq_true_eq] at h1 h2 ⊢
    exact le_trans h2 h1
  have htotal : ∀ a b : ℝ, (decide (b ≤ a) || decide (a ≤ b)) = true := by
    intro a b
    by_cases h : b ≤ a
    · simp [h]
    · simp [h, (le_total b a).resolve_left h]
  have hp := List.pairwise_mergeSort (le := fun a b => decide (b ≤ a)) htrans htotal sigma
  have hsorted : s.SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    simpa [s, decide_eq_true_eq] using hp
  have hant : Antitone s.get := List.sortedGE_iff_antitone_get.mp hsorted
  dsimp [jthLargest, s]
  by_cases hlen : s.length ≤ j - 1
  · rw [List.getD_eq_default s 0 hlen]
    exact hx
  · have hlt : j - 1 < s.length := Nat.lt_of_not_ge hlen
    have hget : s.getD (j - 1) 0 = s.get ⟨j - 1, hlt⟩ := List.getD_eq_get s 0 ⟨j - 1, hlt⟩
    rw [hget]
    by_contra hgt
    have hgt' : x < s.get ⟨j - 1, hlt⟩ := lt_of_not_ge hgt
    -- all positions i <= j-1 have value >= s.get (j-1) > x
    have hall : ∀ i : ℕ, (hi : i < s.length) → i < j →
        decide (x < s.get ⟨i, hi⟩) = true := by
      intro i hi hltj
      have hle_fin : (⟨i, hi⟩ : Fin s.length) ≤ ⟨j - 1, hlt⟩ := by
        exact (by omega : i ≤ j - 1)
      have hant' : s.get ⟨j - 1, hlt⟩ ≤ s.get ⟨i, hi⟩ := hant hle_fin
      rw [decide_eq_true_eq]
      exact lt_of_lt_of_le hgt' hant'
    have hle_count : j ≤ (s.filter fun p => decide (x < p)).length := by
      exact countP_ge_of_forall_getElem s j (by omega) hall
    omega

/-! ### The adversary sequence (Theorem 3.1) -/

/-- Phase-1 job size `a = (1-gamma)(gamma-1/2)`. -/
noncomputable def aVal (m : ℕ) (hm : 4 ≤ m) : ℝ :=
  (1 - gammaVal m hm) * (gammaVal m hm - 1 / 2)

/-- Phase-2 job size `b = gamma(gamma-1/2)`. -/
noncomputable def bVal (m : ℕ) (hm : 4 ≤ m) : ℝ :=
  gammaVal m hm * (gammaVal m hm - 1 / 2)

/-- Phase 1: `m` jobs of size `a`. -/
noncomputable def σ1 (m : ℕ) (hm : 4 ≤ m) : JobSequence :=
  List.replicate m (aVal m hm)

/-- Phases 1+2: `m` jobs of size `a`, then `m` jobs of size `b`. -/
noncomputable def σ2 (m : ℕ) (hm : 4 ≤ m) : JobSequence :=
  σ1 m hm ++ List.replicate m (bVal m hm)

/-- Phases 1+2+3: plus `m-q` jobs of size `1/2`. -/
noncomputable def σ3 (m : ℕ) (hm : 4 ≤ m) : JobSequence :=
  σ2 m hm ++ List.replicate (m - qVal m hm) (1 / 2)

/-- Phases 1-4 with the first `i` jobs of phase 4 (sizes `f_q, ..., f_{q+1-i}`). -/
noncomputable def σ4 (m : ℕ) (hm : 4 ≤ m) (i : ℕ) : JobSequence :=
  σ3 m hm ++ (List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))

/-- All five phases. -/
noncomputable def σ5 (m : ℕ) (hm : 4 ≤ m) : JobSequence :=
  σ4 m hm (qVal m hm) ++ [1]

/-- `gamma_m > 1/2`. -/
lemma gammaVal_gt_half (m : ℕ) (hm : 4 ≤ m) : 1 / 2 < gammaVal m hm := by
  have h := gammaVal_ge_five_seven m hm
  nlinarith

/-- `a + b = gamma - 1/2`. -/
lemma aVal_add_bVal (m : ℕ) (hm : 4 ≤ m) : aVal m hm + bVal m hm = gammaVal m hm - 1 / 2 := by
  dsimp [aVal, bVal]
  ring

/-- `a + 2b = (1+gamma)(gamma - 1/2)`. -/
lemma aVal_add_two_bVal (m : ℕ) (hm : 4 ≤ m) :
    aVal m hm + 2 * bVal m hm = (1 + gammaVal m hm) * (gammaVal m hm - 1 / 2) := by
  dsimp [aVal, bVal]
  ring

/-- `0 <= a`. -/
lemma aVal_nonneg (m : ℕ) (hm : 4 ≤ m) : 0 ≤ aVal m hm := by
  exact mul_nonneg (sub_nonneg.mpr (gammaVal_le_one m hm))
    (sub_nonneg.mpr (le_of_lt (gammaVal_gt_half m hm)))

/-- `0 <= b`. -/
lemma bVal_nonneg (m : ℕ) (hm : 4 ≤ m) : 0 ≤ bVal m hm := by
  exact mul_nonneg (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (gammaVal_gt_half m hm)))
    (sub_nonneg.mpr (le_of_lt (gammaVal_gt_half m hm)))

/-- `b < 1/2`. -/
lemma bVal_lt_half (m : ℕ) (hm : 4 ≤ m) : bVal m hm < 1 / 2 := by
  have hle1 : gammaVal m hm ≤ 1 := gammaVal_le_one m hm
  have hge : 1 / 2 < gammaVal m hm := gammaVal_gt_half m hm
  have hlt1 : gammaVal m hm < 1 := lt_of_le_of_lt (gammaVal_le_alpha m hm) (tanAlpha_lt_one)
  have h1 : gammaVal m hm * (gammaVal m hm - 1 / 2) ≤ 1 * (gammaVal m hm - 1 / 2) :=
    mul_le_mul_of_nonneg_right hle1 (sub_nonneg.mpr (le_of_lt hge))
  have h2 : 1 * (gammaVal m hm - 1 / 2) < 1 / 2 := by nlinarith [hlt1]
  dsimp [bVal]
  nlinarith [h1, h2]

/-- `a <= b`. -/
lemma aVal_le_bVal (m : ℕ) (hm : 4 ≤ m) : aVal m hm ≤ bVal m hm := by
  dsimp [aVal, bVal]
  have hgamma : 1 / 2 < gammaVal m hm := gammaVal_gt_half m hm
  have hpos : 0 ≤ gammaVal m hm - 1 / 2 := sub_nonneg.mpr (le_of_lt hgamma)
  have h : 1 - gammaVal m hm ≤ gammaVal m hm := by nlinarith [hgamma, gammaVal_le_one m hm]
  exact mul_le_mul_of_nonneg_right h hpos

/-- `maxJobSize <= x` when every job is at most `x`. -/
private lemma maxJobSize_le_of_forall {σ : JobSequence} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ p ∈ σ, p ≤ x) : maxJobSize σ ≤ x := by
  have hfold : ∀ (τ : JobSequence) (a : ℝ), (∀ p ∈ τ, p ≤ x) → a ≤ x →
      List.foldl max a τ ≤ x := by
    intro τ
    induction τ with
    | nil => intro a hτ ha; exact ha
    | cons p τ ih =>
        intro a hτ ha
        simp [List.foldl]
        exact ih (max a p) (fun q hq => hτ q (by simp [hq]))
          (max_le ha (hτ p (by simp)))
  dsimp [maxJobSize]
  exact hfold σ 0 h hx

/-- `maxJobSize (replicate n x) = x` for `n > 0` and `0 <= x`. -/
private lemma maxJobSize_replicate {n : ℕ} (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    maxJobSize (List.replicate n x) = x := by
  apply le_antisymm
  · exact maxJobSize_le_of_forall hx (fun p hp => by
      rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
      exact le_rfl)
  · have hmem : x ∈ List.replicate n x := List.mem_replicate.mpr ⟨Nat.ne_of_gt hn, rfl⟩
    exact maxJobSize_ge_each (List.replicate n x) x hmem

/-- If every job of `sigma` is at most `x` and `0 <= x`, then
    `jthLargest sigma j <= x` for any `1 <= j`. -/
private lemma jthLargest_le_of_forall_le {σ : JobSequence} {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ p ∈ σ, p ≤ x) (j : ℕ) (hj : 1 ≤ j) : jthLargest σ j ≤ x := by
  apply jthLargest_le_of_card_lt (j := j) hj hx
  have hf : (σ.filter fun p => decide (x < p)) = [] := by
    induction σ with
    | nil => simp
    | cons a σ ih =>
        have ha : a ≤ x := h a (by simp)
        have hrest : ∀ p ∈ σ, p ≤ x := fun p hp => h p (by simp [hp])
        have ih' : (σ.filter fun p => decide (x < p)) = [] := ih hrest
        simp [List.filter, ih', not_lt_of_ge ha]
  rw [hf]
  simp
  omega

/-- `filter p (replicate n x) = if p x then replicate n x else []`. -/
private lemma filter_replicate (p : ℝ → Bool) (n : ℕ) (x : ℝ) :
    (List.replicate n x).filter p = if p x then List.replicate n x else [] := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hpx : p x = true
      · simp [List.replicate, hpx, ih]
      · simp [List.replicate, hpx, ih]

/-- `a < b` strictly. -/
private lemma aVal_lt_bVal (m : ℕ) (hm : 4 ≤ m) : aVal m hm < bVal m hm := by
  dsimp [aVal, bVal]
  have hgamma : 1 / 2 < gammaVal m hm := gammaVal_gt_half m hm
  have hpos : 0 < gammaVal m hm - 1 / 2 := sub_pos.mpr hgamma
  have h : 1 - gammaVal m hm < gammaVal m hm := by nlinarith [hgamma]
  exact mul_lt_mul_of_pos_right h hpos

/-- In `sigma2` exactly `m` jobs are larger than `a`. -/
private lemma count_gt_a_σ2 (m : ℕ) (hm : 4 ≤ m) :
    ((σ2 m hm).filter fun p => decide (aVal m hm < p)).length = m := by
  dsimp [σ2, σ1]
  rw [List.filter_append]
  have hna : decide (aVal m hm < aVal m hm) = false := by simp
  have hpb : decide (aVal m hm < bVal m hm) = true := by
    rw [decide_eq_true_eq]
    exact aVal_lt_bVal m hm
  rw [filter_replicate _ m (aVal m hm), filter_replicate _ m (bVal m hm)]
  rw [hna, hpb]
  simp

/-- `LB3(m, sigma1) = 0`. -/
lemma LB3_σ1 (m : ℕ) (hm : 4 ≤ m) : LB3 m (σ1 m hm) = 0 := by
  have hdiv : (m - 1) / m = 0 := by
    exact Nat.div_eq_of_lt (by omega)
  dsimp [LB3, σ1]
  simp [hdiv]

/-- `PseudoLB(m, sigma1) = a`. -/
lemma PseudoLBGen_σ1 (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ1 m hm) = aVal m hm := by
  have htotal : totalLoad (σ1 m hm) = (m : ℝ) * aVal m hm := by
    dsimp [σ1, totalLoad]
    simp
  have hmax : maxJobSize (σ1 m hm) = aVal m hm := by
    exact maxJobSize_replicate (by omega : 0 < m) (aVal m hm) (aVal_nonneg m hm)
  have hlb3 : LB3 m (σ1 m hm) = 0 := LB3_σ1 m hm
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  dsimp [PseudoLBGen]
  rw [htotal, hmax, hlb3]
  have h1 : (m : ℝ) * aVal m hm / (m : ℝ) = aVal m hm := by
    field_simp [hm_pos.ne']
  rw [h1]
  simp [aVal_nonneg m hm]

/-- `PseudoLB(m, sigma2) = gamma - 1/2`. -/
lemma PseudoLBGen_σ2 (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ2 m hm) = gammaVal m hm - 1 / 2 := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have htotal : totalLoad (σ2 m hm) = (m : ℝ) * (aVal m hm + bVal m hm) := by
    dsimp [σ2, σ1, totalLoad]
    simp
    ring
  have hb_le : bVal m hm ≤ gammaVal m hm - 1 / 2 := by
    have hg : 1 / 2 < gammaVal m hm := gammaVal_gt_half m hm
    dsimp [bVal]
    nlinarith [hg, gammaVal_le_one m hm]
  have hmax_le : maxJobSize (σ2 m hm) ≤ gammaVal m hm - 1 / 2 := by
    have hle : maxJobSize (σ2 m hm) ≤ bVal m hm := by
      exact maxJobSize_le_of_forall (bVal_nonneg m hm) (fun p hp => by
        rcases List.mem_append.mp hp with hp1 | hp2
        · rcases List.mem_replicate.mp hp1 with ⟨_, rfl⟩
          exact aVal_le_bVal m hm
        · rcases List.mem_replicate.mp hp2 with ⟨_, rfl⟩
          exact le_rfl)
    exact le_trans hle hb_le
  -- LB3: k ranges over Icc 1 1; p_(m) + p_(m+1) <= b + a
  have hk : ((σ2 m hm).length - 1) / m = 1 := by
    dsimp [σ2, σ1]
    simp
    rw [Nat.div_eq_of_lt_le (k := 1) (n := m) (m := m + m - 1)]
    · omega
    · have h2 : (1 + 1) * m = 2 * m := by ring
      omega
  have hjth_b : jthLargest (σ2 m hm) m ≤ bVal m hm := by
    apply jthLargest_le_of_forall_le (bVal_nonneg m hm)
    · intro p hp
      rcases List.mem_append.mp hp with hp1 | hp2
      · rcases List.mem_replicate.mp hp1 with ⟨_, rfl⟩
        exact aVal_le_bVal m hm
      · rcases List.mem_replicate.mp hp2 with ⟨_, rfl⟩
        exact le_rfl
    · omega
  have hjth_a : jthLargest (σ2 m hm) (m + 1) ≤ aVal m hm := by
    apply jthLargest_le_of_card_lt (by omega : 1 ≤ m + 1) (aVal_nonneg m hm)
    rw [count_gt_a_σ2 m hm]
    omega
  have hlb3_le : LB3 m (σ2 m hm) ≤ gammaVal m hm - 1 / 2 := by
    dsimp [LB3]
    rw [hk]
    simp
    have hval : (∑ j ∈ Finset.Icc (m - 1 + 1) (m + 1), jthLargest (σ2 m hm) j) ≤
        gammaVal m hm - (2 : ℝ)⁻¹ := by
      have hsum : (∑ j ∈ Finset.Icc (m - 1 + 1) (m + 1), jthLargest (σ2 m hm) j) =
          jthLargest (σ2 m hm) m + jthLargest (σ2 m hm) (m + 1) := by
        have hIcc : Finset.Icc (m - 1 + 1) (m + 1) = ({m, m + 1} : Finset ℕ) := by
          ext j
          simp [Finset.mem_Icc]
          omega
        rw [hIcc]
        simp
      rw [hsum]
      have hab : aVal m hm + bVal m hm = gammaVal m hm - (2 : ℝ)⁻¹ := by
        simpa [one_div] using aVal_add_bVal m hm
      nlinarith [hjth_b, hjth_a, hab]
    exact hval
  -- LB1 = gamma - 1/2
  have hlb1 : totalLoad (σ2 m hm) / (m : ℝ) = gammaVal m hm - 1 / 2 := by
    rw [htotal]
    rw [aVal_add_bVal m hm]
    field_simp [hm_pos.ne']
  dsimp [PseudoLBGen]
  rw [hlb1]
  have hmax1 : max (maxJobSize (σ2 m hm)) (LB3 m (σ2 m hm)) ≤ gammaVal m hm - 1 / 2 :=
    max_le hmax_le hlb3_le
  exact le_antisymm (max_le (le_rfl) hmax1) (le_max_left _ _)

/-- `2a <= b` (from `gamma >= 5/7`). -/
private lemma two_aVal_le_bVal (m : ℕ) (hm : 4 ≤ m) : 2 * aVal m hm ≤ bVal m hm := by
  dsimp [aVal, bVal]
  have hg : (5 / 7 : ℝ) ≤ gammaVal m hm := gammaVal_ge_five_seven m hm
  have hpos : 0 ≤ gammaVal m hm - 1 / 2 := sub_nonneg.mpr (le_of_lt (gammaVal_gt_half m hm))
  have h : 2 * (1 - gammaVal m hm) ≤ gammaVal m hm := by nlinarith [hg]
  nlinarith

/-- In `sigma3` exactly `m-q` jobs are larger than `b`. -/
private lemma count_gt_b_σ3 (m : ℕ) (hm : 4 ≤ m) :
    ((σ3 m hm).filter fun p => decide (bVal m hm < p)).length = m - qVal m hm := by
  dsimp [σ3, σ2, σ1]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [filter_replicate _ m (aVal m hm), filter_replicate _ m (bVal m hm),
      filter_replicate _ (m - qVal m hm) (1 / 2)]
  have hna : decide (bVal m hm < aVal m hm) = false := by
    simp [not_lt_of_ge (aVal_le_bVal m hm)]
  have hnb : decide (bVal m hm < bVal m hm) = false := by simp
  have hnh : decide (bVal m hm < 1 / 2) = true := by
    rw [decide_eq_true_eq]
    exact bVal_lt_half m hm
  rw [hna, hnb, hnh]
  simp

/-- In `sigma3` exactly `2m-q` jobs are larger than `a`. -/
private lemma count_gt_a_σ3 (m : ℕ) (hm : 4 ≤ m) :
    ((σ3 m hm).filter fun p => decide (aVal m hm < p)).length = 2 * m - qVal m hm := by
  dsimp [σ3, σ2, σ1]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [filter_replicate _ m (aVal m hm), filter_replicate _ m (bVal m hm),
      filter_replicate _ (m - qVal m hm) (1 / 2)]
  have hna : decide (aVal m hm < aVal m hm) = false := by simp
  have hnb : decide (aVal m hm < bVal m hm) = true := by
    rw [decide_eq_true_eq]
    exact aVal_lt_bVal m hm
  have hnh : decide (aVal m hm < 1 / 2) = true := by
    rw [decide_eq_true_eq]
    exact lt_trans (aVal_lt_bVal m hm) (bVal_lt_half m hm)
  rw [hna, hnb, hnh]
  simp
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  omega

private lemma jthLargest_σ3_pos_le_b (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : 1 ≤ j)
    (hjb : m - qVal m hm < j) : jthLargest (σ3 m hm) j ≤ bVal m hm := by
  apply jthLargest_le_of_card_lt hj (bVal_nonneg m hm)
  rw [count_gt_b_σ3 m hm]
  exact hjb

private lemma jthLargest_σ3_pos_le_a (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : 1 ≤ j)
    (hja : 2 * m - qVal m hm < j) : jthLargest (σ3 m hm) j ≤ aVal m hm := by
  apply jthLargest_le_of_card_lt hj (aVal_nonneg m hm)
  rw [count_gt_a_σ3 m hm]
  exact hja

/-- `LB3(m, sigma3) <= 2b`. -/
lemma LB3_σ3_le_two_b (m : ℕ) (hm : 4 ≤ m) : LB3 m (σ3 m hm) ≤ 2 * bVal m hm := by
  classical
  have hk : ((σ3 m hm).length - 1) / m = 2 := by
    dsimp [σ3, σ2, σ1]
    simp
    have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
    have hlen : m + (m + (m - qVal m hm)) - 1 = 3 * m - qVal m hm - 1 := by omega
    rw [hlen]
    rw [Nat.div_eq_of_lt_le (k := 2) (n := m) (m := 3 * m - qVal m hm - 1)]
    · have hq_le_m1 : qVal m hm ≤ m - 1 := by
        have hqt : qVal m hm ≤ tVal m := qVal_le_t m hm
        have ht : tVal m ≤ m - 1 := by dsimp [tVal]; omega
        omega
      omega
    · have h2 : (2 + 1) * m = 3 * m := by ring
      rw [h2]
      have hq : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
      have hle1 : 3 * m - qVal m hm - 1 ≤ 3 * m - 1 := by omega
      have hlt1 : 3 * m - 1 < 3 * m := by omega
      omega
  have hnon : (Finset.Icc 1 2 : Finset ℕ).Nonempty := by simp
  dsimp [LB3]
  rw [hk]
  have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
  have hb_m : m - qVal m hm < m := by omega
  have hb_m1 : m - qVal m hm < m + 1 := by omega
  have hb_2m1 : m - qVal m hm < 2 * m - 1 := by omega
  have ha_2m : 2 * m - qVal m hm < 2 * m := by omega
  have ha_2m1 : 2 * m - qVal m hm < 2 * m + 1 := by omega
  have h1 : jthLargest (σ3 m hm) m ≤ bVal m hm :=
    jthLargest_σ3_pos_le_b m hm m (by omega) hb_m
  have h2 : jthLargest (σ3 m hm) (m + 1) ≤ bVal m hm :=
    jthLargest_σ3_pos_le_b m hm (m + 1) (by omega) hb_m1
  have h3 : jthLargest (σ3 m hm) (2 * m - 1) ≤ bVal m hm :=
    jthLargest_σ3_pos_le_b m hm (2 * m - 1) (by omega) hb_2m1
  have h4 : jthLargest (σ3 m hm) (2 * m) ≤ aVal m hm :=
    jthLargest_σ3_pos_le_a m hm (2 * m) (by omega) ha_2m
  have h5 : jthLargest (σ3 m hm) (2 * m + 1) ≤ aVal m hm :=
    jthLargest_σ3_pos_le_a m hm (2 * m + 1) (by omega) ha_2m1
  have h2a : 2 * aVal m hm ≤ bVal m hm := two_aVal_le_bVal m hm
  have hb2 : bVal m hm + 2 * aVal m hm ≤ 2 * bVal m hm := by nlinarith [h2a]
  have hf1 : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ3 m hm) j) ≤ 2 * bVal m hm := by
    have hsum : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ3 m hm) j) =
        jthLargest (σ3 m hm) m + jthLargest (σ3 m hm) (m + 1) := by
      have hIcc : Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1) = ({m, m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        omega
      rw [hIcc]
      simp
    rw [hsum]
    nlinarith [h1, h2]
  have hf2 : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ3 m hm) j) ≤ 2 * bVal m hm := by
    have hsum : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ3 m hm) j) =
        jthLargest (σ3 m hm) (2 * m - 1) + jthLargest (σ3 m hm) (2 * m) +
          jthLargest (σ3 m hm) (2 * m + 1) := by
      have hIcc : Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1) = ({2 * m - 1, 2 * m, 2 * m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        have hnorm : m * 2 = 2 * m := by ring
        rw [hnorm]
        omega
      rw [hIcc]
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_singleton]
          ring
        · intro h
          simp at h
      · intro h
        simp at h
        omega
    rw [hsum]
    nlinarith [h3, h4, h5, hb2]
  by_cases hc : (Finset.Icc 1 2).Nonempty
  · rw [dif_pos hc]
    apply Finset.sup'_le
    intro k hk1
    have hk12 : k = 1 ∨ k = 2 := by
      rw [Finset.mem_Icc] at hk1
      omega
    rcases hk12 with rfl | rfl
    · exact hf1
    · exact hf2
  · exfalso
    exact hc hnon

/-- `LB1(m, sigma3) <= (gamma + 1/2)/(1 + gamma)`. -/
lemma LB1_σ3_le (m : ℕ) (hm : 4 ≤ m) :
    totalLoad (σ3 m hm) / (m : ℝ) ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
  have hβmem : betaVal m hm ∈ Set.Icc (0 : ℝ) 1 :=
    xRoot_mem_unit hm (qVal_ge_one m hm) (qVal_le_t m hm)
  have hβ_nonneg : 0 ≤ betaVal m hm := hβmem.1
  have htop1 : 1 + betaVal m hm ≠ 0 := by nlinarith
  have hgβ : gVal m (betaVal m hm) (qVal m hm) = 1 / 2 := by
    dsimp [betaVal]
    exact xRoot_eq m (qVal m hm) hm (qVal_ge_one m hm) (qVal_le_t m hm)
  have hclosed := gVal_closed m (by omega) (betaVal m hm) (qVal m hm) (by omega) htop1
  have hmain : betaVal m hm ^ 2 - fVal m (betaVal m hm) (qVal m hm + 1) =
      (1 + betaVal m hm) * (qVal m hm : ℝ) / (2 * (m : ℝ)) := by
    have hmul : (m : ℝ) / ((1 + betaVal m hm) * (qVal m hm : ℝ)) *
        (betaVal m hm ^ 2 - fVal m (betaVal m hm) (qVal m hm + 1)) = 1 / 2 := by
      rw [← hclosed]
      exact hgβ
    have hq_ne : (qVal m hm : ℝ) ≠ 0 := by exact_mod_cast (by omega : qVal m hm ≠ 0)
    field_simp [htop1, hq_ne, hm_pos.ne'] at hmul
    field_simp [hm_pos.ne']
    nlinarith [hmul]
  have hγ_le_β : gammaVal m hm ≤ betaVal m hm := gammaVal_le_beta m hm
  have hf_le : fVal m (betaVal m hm) (qVal m hm + 1) ≤ 1 / 2 := (fVal_gamma_chain m hm).1
  have hmain2 : gammaVal m hm - (qVal m hm : ℝ) / (2 * (m : ℝ)) ≤
      (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
    have hsub : (qVal m hm : ℝ) / (2 * (m : ℝ)) =
        (betaVal m hm ^ 2 - fVal m (betaVal m hm) (qVal m hm + 1)) / (1 + betaVal m hm) := by
      field_simp [hm_pos.ne'] at hmain
      field_simp [htop1, hm_pos.ne']
      nlinarith [hmain]
    rw [hsub]
    have hden1 : 0 < 1 + betaVal m hm := by nlinarith
    have hnum : 0 ≤ gammaVal m hm + 1 / 2 := by nlinarith [gammaVal_gt_half m hm]
    have hstep1 : gammaVal m hm - (betaVal m hm ^ 2 - fVal m (betaVal m hm) (qVal m hm + 1)) /
        (1 + betaVal m hm) ≤ (gammaVal m hm + 1 / 2) / (1 + betaVal m hm) := by
      field_simp [hden1.ne']
      nlinarith [hγ_le_β, hf_le]
    have hstep2 : (gammaVal m hm + 1 / 2) / (1 + betaVal m hm) ≤
        (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
      have hden2 : 0 < 1 + gammaVal m hm := by nlinarith [gammaVal_gt_half m hm]
      have hle' : (1 + gammaVal m hm) ≤ (1 + betaVal m hm) := by nlinarith [hγ_le_β]
      have hcross : (gammaVal m hm + 1 / 2) * (1 + gammaVal m hm) ≤
          (gammaVal m hm + 1 / 2) * (1 + betaVal m hm) :=
        mul_le_mul_of_nonneg_left hle' hnum
      rw [div_le_div_iff₀ hden1 hden2]
      exact hcross
    exact le_trans hstep1 hstep2
  -- totalLoad(σ3)/m = γ − q/2m
  have htotal : totalLoad (σ3 m hm) / (m : ℝ) = gammaVal m hm - (qVal m hm : ℝ) / (2 * (m : ℝ)) := by
    dsimp [σ3, σ2, σ1, totalLoad]
    simp
    field_simp [hm_pos.ne']
    have hmn : (↑(m - qVal m hm) : ℝ) = (m : ℝ) - (qVal m hm : ℝ) := by
      have hq_le : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      exact Nat.cast_sub hq_le
    rw [hmn]
    nlinarith [aVal_add_bVal m hm]
  rw [htotal]
  exact hmain2

/-- `PseudoLB(m, sigma3) <= (gamma + 1/2)/(1 + gamma)`. -/
lemma PseudoLBGen_σ3_le (m : ℕ) (hm : 4 ≤ m) :
    PseudoLBGen m (σ3 m hm) ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
  have hmax_le : maxJobSize (σ3 m hm) ≤ 1 / 2 := by
    exact maxJobSize_le_of_forall (by norm_num) (fun p hp => by
      rcases List.mem_append.mp hp with hp2 | hp3
      · rcases List.mem_append.mp hp2 with hp1 | hp2'
        · rcases List.mem_replicate.mp hp1 with ⟨_, rfl⟩
          exact le_trans (aVal_le_bVal m hm) (le_of_lt (bVal_lt_half m hm))
        · rcases List.mem_replicate.mp hp2' with ⟨_, rfl⟩
          exact le_of_lt (bVal_lt_half m hm)
      · rcases List.mem_replicate.mp hp3 with ⟨_, rfl⟩
        exact le_rfl)
  have hlb1 := LB1_σ3_le m hm
  have hlb2 : 1 / 2 ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
    have hden : 0 < 1 + gammaVal m hm := by nlinarith [gammaVal_gt_half m hm]
    rw [le_div_iff₀ hden]
    nlinarith [gammaVal_gt_half m hm]
  have hlb3 : 2 * bVal m hm ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
    have hb13 : 2 * bVal m hm ≤ 2 / 3 := by
      have h := gammaVal_mul_le_one_third m hm
      dsimp [bVal]
      nlinarith
    have h23 : 2 / 3 ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
      have hden : 0 < 1 + gammaVal m hm := by nlinarith [gammaVal_gt_half m hm]
      rw [le_div_iff₀ hden]
      nlinarith [gammaVal_gt_half m hm]
    nlinarith
  dsimp [PseudoLBGen]
  exact max_le (le_trans hlb1 (by rfl)) (max_le (le_trans hmax_le hlb2) (le_trans (LB3_σ3_le_two_b m hm) hlb3))

/-! ### Phase 4 (continued): the phase-4 prefixes -/

/-- `f_j(gamma) >= 1/2` for `j <= q`. -/
lemma fVal_ge_half_of_le_q (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : j ≤ qVal m hm) :
    1 / 2 ≤ fVal m (gammaVal m hm) j := by
  have hchain := fVal_gamma_chain m hm
  have hq : 1 / 2 ≤ fVal m (gammaVal m hm) (qVal m hm) := hchain.2.1
  have hsucc : ∀ k : ℕ, fVal m (gammaVal m hm) (k + 1) ≤ fVal m (gammaVal m hm) k := by
    intro k
    have hc_pos : 0 < cVal m (gammaVal m hm) := by
      dsimp [cVal]
      have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hg1 : gammaVal m hm < 1 := lt_of_le_of_lt (gammaVal_le_alpha m hm) (tanAlpha_lt_one)
      have hnum : 0 < (m : ℝ) - 1 - gammaVal m hm := by
        have h3 : (3 : ℝ) - gammaVal m hm > 2 := by nlinarith [hg1]
        have h4 : (m : ℝ) - 1 - gammaVal m hm ≥ (3 : ℝ) - gammaVal m hm := by nlinarith [hmr]
        nlinarith
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      exact div_pos hnum hm_pos
    have hc_le : cVal m (gammaVal m hm) ≤ 1 := by
      dsimp [cVal]
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hg : 0 ≤ gammaVal m hm := le_trans (by norm_num) (gammaVal_ge_five_seven m hm)
      have hnum : (m : ℝ) - 1 - gammaVal m hm ≤ (m : ℝ) := by nlinarith [hg]
      exact (div_le_one₀ hm_pos).2 hnum
    dsimp [fVal]
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (le_of_lt hc_pos) k) hc_le
  by_cases hj0 : j = 0
  · subst j
    dsimp [fVal]
    norm_num
  · have hj1 : 1 ≤ j := by omega
    have hdesc : fVal m (gammaVal m hm) (qVal m hm) ≤ fVal m (gammaVal m hm) j := by
      have hmain : ∀ d : ℕ, ∀ j' : ℕ, j' ≤ qVal m hm → qVal m hm - j' = d →
          fVal m (gammaVal m hm) (qVal m hm) ≤ fVal m (gammaVal m hm) j' := by
        intro d
        induction d with
        | zero =>
            intro j' hle hqj
            have hjq : j' = qVal m hm := by omega
            rw [hjq]
        | succ d ih =>
            intro j' hle hqj
            have hsubpos : 0 < qVal m hm - j' := by
              rw [hqj]
              omega
            have hlt : j' < qVal m hm := Nat.lt_of_sub_pos hsubpos
            have hstep : fVal m (gammaVal m hm) (j' + 1) ≤ fVal m (gammaVal m hm) j' :=
              hsucc j'
            have hih : fVal m (gammaVal m hm) (qVal m hm) ≤ fVal m (gammaVal m hm) (j' + 1) := by
              have hqj1 : qVal m hm - (j' + 1) = d := by
                have hq : qVal m hm = d + 1 + j' :=
                  (Nat.sub_eq_iff_eq_add (le_of_lt hlt)).mp hqj
                have hq' : qVal m hm = j' + (d + 1) := by omega
                rw [hq']
                rw [Nat.add_sub_add_left]
                omega
              have hle1 : j' + 1 ≤ qVal m hm := by omega
              exact ih (j' + 1) hle1 hqj1
            exact le_trans hih hstep
      exact hmain (qVal m hm - j) j hj rfl
    exact le_trans hq hdesc

/-- `f_{j+1}(gamma) <= f_j(gamma)` for all `j`. -/
lemma fVal_succ_le (m : ℕ) (hm : 4 ≤ m) (j : ℕ) :
    fVal m (gammaVal m hm) (j + 1) ≤ fVal m (gammaVal m hm) j := by
  have hc_pos : 0 < cVal m (gammaVal m hm) := by
    dsimp [cVal]
    have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hg1 : gammaVal m hm < 1 := lt_of_le_of_lt (gammaVal_le_alpha m hm) (tanAlpha_lt_one)
    have hnum : 0 < (m : ℝ) - 1 - gammaVal m hm := by
      have h3 : (3 : ℝ) - gammaVal m hm > 2 := by nlinarith [hg1]
      have h4 : (m : ℝ) - 1 - gammaVal m hm ≥ (3 : ℝ) - gammaVal m hm := by nlinarith [hmr]
      nlinarith
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    exact div_pos hnum hm_pos
  have hc_le : cVal m (gammaVal m hm) ≤ 1 := by
    dsimp [cVal]
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hg : 0 ≤ gammaVal m hm := le_trans (by norm_num) (gammaVal_ge_five_seven m hm)
    have hnum : (m : ℝ) - 1 - gammaVal m hm ≤ (m : ℝ) := by nlinarith [hg]
    exact (div_le_one₀ hm_pos).2 hnum
  dsimp [fVal]
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg (le_of_lt hc_pos) j) hc_le

/-- The sum of the first `i` phase-4 jobs, `f_q + ... + f_{q+1-i}`. -/
noncomputable def phase4Sum (m : ℕ) (hm : 4 ≤ m) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (qVal m hm + 1 - i) (qVal m hm), fVal m (gammaVal m hm) j

/-- The total processing time of the first `i` phase-4 jobs equals `phase4Sum`. -/
private lemma phase4_totalLoad (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : i ≤ qVal m hm) :
    ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).sum =
      phase4Sum m hm i := by
  induction i with
  | zero =>
      simp [phase4Sum]
  | succ i ih =>
      have hi' : i ≤ qVal m hm := by omega
      have hsum : ((List.range (i + 1)).map
          (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).sum =
          ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).sum +
            fVal m (gammaVal m hm) (qVal m hm - i) := by
        rw [List.range_succ, List.map_append, List.sum_append]
        simp
      rw [hsum, ih hi']
      dsimp [phase4Sum]
      have hIcc : Finset.Icc (qVal m hm + 1 - (i + 1)) (qVal m hm) =
          insert (qVal m hm - i) (Finset.Icc (qVal m hm + 1 - i) (qVal m hm)) := by
        ext j
        simp [Finset.mem_Icc]
        omega
      rw [hIcc]
      have hnot : qVal m hm - i ∉ Finset.Icc (qVal m hm + 1 - i) (qVal m hm) := by
        intro h
        rw [Finset.mem_Icc] at h
        have hle : qVal m hm + 1 - i ≤ qVal m hm - i := h.1
        have hle' : (qVal m hm + 1 - i) + i ≤ (qVal m hm - i) + i :=
          Nat.add_le_add_right hle i
        have hc1 : (qVal m hm + 1 - i) + i = qVal m hm + 1 := by
          exact Nat.sub_add_cancel (by omega : i ≤ qVal m hm + 1)
        have hc2 : (qVal m hm - i) + i = qVal m hm := Nat.sub_add_cancel hi'
        rw [hc1, hc2] at hle'
        omega
      rw [Finset.sum_insert hnot]
      ring

/-- Every phase-4 job is larger than `b`. -/
private lemma phase4_gt_b (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).filter
        (fun p => decide (bVal m hm < p)) =
      (List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j)) := by
  apply List.filter_eq_self.mpr
  intro p hp
  rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
  rw [decide_eq_true_eq]
  exact lt_of_lt_of_le (bVal_lt_half m hm)
    (fVal_ge_half_of_le_q m hm (qVal m hm - j) (by omega))

/-- Every phase-4 job is larger than `a`. -/
private lemma phase4_gt_a (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).filter
        (fun p => decide (aVal m hm < p)) =
      (List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j)) := by
  apply List.filter_eq_self.mpr
  intro p hp
  rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
  rw [decide_eq_true_eq]
  exact lt_trans (aVal_lt_bVal m hm) (lt_of_lt_of_le (bVal_lt_half m hm)
    (fVal_ge_half_of_le_q m hm (qVal m hm - j) (by omega)))

/-- In `sigma4_i` exactly `m - q + i` jobs are larger than `b`. -/
private lemma count_gt_b_σ4 (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    ((σ4 m hm i).filter fun p => decide (bVal m hm < p)).length = m - qVal m hm + i := by
  dsimp [σ4, σ3, σ2, σ1]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [filter_replicate _ m (aVal m hm), filter_replicate _ m (bVal m hm),
      filter_replicate _ (m - qVal m hm) (1 / 2)]
  rw [phase4_gt_b]
  have hna : decide (bVal m hm < aVal m hm) = false := by
    simp [not_lt_of_ge (aVal_le_bVal m hm)]
  have hnb : decide (bVal m hm < bVal m hm) = false := by simp
  have hnh : decide (bVal m hm < 1 / 2) = true := by
    rw [decide_eq_true_eq]
    exact bVal_lt_half m hm
  rw [hna, hnb, hnh]
  simp

/-- In `sigma4_i` exactly `2m - q + i` jobs are larger than `a`. -/
private lemma count_gt_a_σ4 (m : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    ((σ4 m hm i).filter fun p => decide (aVal m hm < p)).length = 2 * m - qVal m hm + i := by
  dsimp [σ4, σ3, σ2, σ1]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [List.filter_append]
  rw [filter_replicate _ m (aVal m hm), filter_replicate _ m (bVal m hm),
      filter_replicate _ (m - qVal m hm) (1 / 2)]
  rw [phase4_gt_a]
  have hna : decide (aVal m hm < aVal m hm) = false := by simp
  have hnb : decide (aVal m hm < bVal m hm) = true := by
    rw [decide_eq_true_eq]
    exact aVal_lt_bVal m hm
  have hnh : decide (aVal m hm < 1 / 2) = true := by
    rw [decide_eq_true_eq]
    exact lt_trans (aVal_lt_bVal m hm) (bVal_lt_half m hm)
  rw [hna, hnb, hnh]
  simp
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  omega

/-- `f_1(gamma) = (m-1-gamma)/m`. -/
lemma fVal_one_gamma (m : ℕ) (hm : 4 ≤ m) :
    fVal m (gammaVal m hm) 1 = ((m : ℝ) - 1 - gammaVal m hm) / (m : ℝ) := by
  dsimp [fVal, cVal]
  simp

/-- The phase-4 partial sum splits off the first `q-i` terms. -/
private lemma phase4Sum_split (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : i ≤ qVal m hm) :
    phase4Sum m hm i +
      (∑ j ∈ Finset.Icc 1 (qVal m hm - i), fVal m (gammaVal m hm) j) =
      (∑ j ∈ Finset.Icc 1 (qVal m hm), fVal m (gammaVal m hm) j) := by
  dsimp [phase4Sum]
  by_cases hiq : qVal m hm - i = 0
  · have hqi : i = qVal m hm := by omega
    subst i
    simp
  · have hmn : 1 ≤ qVal m hm - i := by omega
    have hU : Finset.Icc 1 (qVal m hm - i) ∪ Finset.Icc (qVal m hm + 1 - i) (qVal m hm) =
        Finset.Icc 1 (qVal m hm) := by
      ext j
      simp [Finset.mem_Icc]
      omega
    have hD : Disjoint (Finset.Icc 1 (qVal m hm - i))
        (Finset.Icc (qVal m hm + 1 - i) (qVal m hm)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      rw [Finset.mem_Icc] at hj1 hj2
      omega
    rw [← hU]
    rw [Finset.sum_union hD]
    rw [add_comm]

/-- `LB1(m, sigma4_i) <= (gamma + f_{q+1-i}(gamma))/(1 + gamma)`. -/
lemma LB1_σ4_le (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ qVal m hm) :
    totalLoad (σ4 m hm i) / (m : ℝ) ≤
      (gammaVal m hm + fVal m (gammaVal m hm) (qVal m hm + 1 - i)) / (1 + gammaVal m hm) := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
  have hg_nonneg : 0 ≤ gammaVal m hm := le_trans (by norm_num) (gammaVal_ge_five_seven m hm)
  have hgtop1 : 1 + gammaVal m hm ≠ 0 := by nlinarith [hg_nonneg]
  have hγ_le_β : gammaVal m hm ≤ betaVal m hm := gammaVal_le_beta m hm
  -- the total load identity
  have htotal : totalLoad (σ4 m hm i) / (m : ℝ) =
      gammaVal m hm - 1 / 2 +
        (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 + phase4Sum m hm i) := by
    dsimp [σ4, σ3, σ2, σ1, totalLoad]
    simp
    rw [phase4_totalLoad m hm i hi_le]
    field_simp [hm_pos.ne']
    have hmn : (↑(m - qVal m hm) : ℝ) = (m : ℝ) - (qVal m hm : ℝ) := by
      have hq_le : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      exact Nat.cast_sub hq_le
    nlinarith [aVal_add_bVal m hm, hmn]
  rw [htotal]
  -- chain: use Lemma 2.6(iii) and (4)
  have hmain3 := gammaVal_main_ineq m hm
  have hgeom := fVal_sum_geometric m (gammaVal m hm) (qVal m hm - i) hgtop1 (by omega)
  have hsplit := phase4Sum_split m hm i hi_le
  have hf1 : fVal m (gammaVal m hm) 1 = ((m : ℝ) - 1 - gammaVal m hm) / (m : ℝ) :=
    fVal_one_gamma m hm
  have hidx : fVal m (gammaVal m hm) ((qVal m hm - i) + 1) =
      fVal m (gammaVal m hm) (qVal m hm + 1 - i) := by
    congr 1
    exact (Nat.sub_add_comm hi_le).symm
  -- target after rewriting: (γ − 1/2 + (1/m)[(m−q)/2 + S_i]) ≤ (γ + f)/(1+γ)
  -- S_i = S_q − S_{q−i} — from hsplit: S_i + S_{q−i} = S_q
  -- S_q bound by 2.6(iii); S_{q−i} = (m/(1+γ))(f_1 − f_{q−i+1}) by (4)
  have hchain :
      gammaVal m hm - 1 / 2 +
        (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 + phase4Sum m hm i) ≤
      (gammaVal m hm + fVal m (gammaVal m hm) (qVal m hm + 1 - i)) / (1 + gammaVal m hm) := by
    have hSq : gammaVal m hm - 1 / 2 +
        (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 +
          (∑ j ∈ Finset.Icc 1 (qVal m hm), fVal m (gammaVal m hm) j)) ≤
        ((m : ℝ) - 1) / (m : ℝ) := hmain3
    have hSm : (∑ j ∈ Finset.Icc 1 (qVal m hm - i), fVal m (gammaVal m hm) j) =
        (m : ℝ) / (1 + gammaVal m hm) *
          (fVal m (gammaVal m hm) 1 - fVal m (gammaVal m hm) ((qVal m hm - i) + 1)) := hgeom
    -- algebra: substitute hsplit, hSm, hf1, hidx into the target
    field_simp [hm_pos.ne', hgtop1] at hSq hSm hf1 ⊢
    nlinarith [hSq, hsplit, hSm, hf1, hidx, hγ_le_β]
  exact hchain

/-- At most `q` jobs of `sigma4_i` are larger than `1/2`. -/
private lemma count_gt_half_σ4_le (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : i ≤ qVal m hm) :
    ((σ4 m hm i).filter fun p => decide (1 / 2 < p)).length ≤ qVal m hm := by
  have hna : decide (1 / 2 < aVal m hm) = false := by
    rw [decide_eq_false_iff_not]
    exact not_lt_of_ge (le_trans (aVal_le_bVal m hm) (le_of_lt (bVal_lt_half m hm)))
  have hnb : decide (1 / 2 < bVal m hm) = false := by
    rw [decide_eq_false_iff_not]
    exact not_lt_of_ge (le_of_lt (bVal_lt_half m hm))
  have hnh : decide ((1 : ℝ) / 2 < (1 : ℝ) / 2) = false := by
    rw [decide_eq_false_iff_not]
    exact (lt_irrefl ((1 : ℝ) / 2))
  have hfa : (List.replicate m (aVal m hm)).filter (fun p => decide (1 / 2 < p)) = [] := by
    rw [filter_replicate _ m (aVal m hm)]
    rw [hna]
    simp
  have hfb : (List.replicate m (bVal m hm)).filter (fun p => decide (1 / 2 < p)) = [] := by
    rw [filter_replicate _ m (bVal m hm)]
    rw [hnb]
    simp
  have hfh : (List.replicate (m - qVal m hm) (1 / 2)).filter (fun p => decide (1 / 2 < p)) = [] := by
    induction (m - qVal m hm) with
    | zero => simp
    | succ n ih =>
        simp [List.replicate, List.filter, hnh, ih]
  have hσ3 : (σ3 m hm).filter (fun p => decide (1 / 2 < p)) = [] := by
    have hall : ∀ p ∈ σ3 m hm, p ≤ 1 / 2 := by
      intro p hp
      rcases List.mem_append.mp hp with hp2 | hp3
      · rcases List.mem_append.mp hp2 with hp1 | hp2'
        · rcases List.mem_replicate.mp hp1 with ⟨_, rfl⟩
          exact le_trans (aVal_le_bVal m hm) (le_of_lt (bVal_lt_half m hm))
        · rcases List.mem_replicate.mp hp2' with ⟨_, rfl⟩
          exact le_of_lt (bVal_lt_half m hm)
      · rcases List.mem_replicate.mp hp3 with ⟨_, rfl⟩
        exact le_rfl
    have hgeneral : ∀ l : JobSequence, (∀ p ∈ l, p ≤ 1 / 2) →
        l.filter (fun p => decide (1 / 2 < p)) = [] := by
      intro l
      induction l with
      | nil => intro hall'; simp
      | cons a l ih =>
          intro hall'
          have ha' : ¬ ((2 : ℝ)⁻¹ < a) := by
            have h1 : a ≤ 1 / 2 := hall' a (by simp)
            have hz : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
            intro h2
            nlinarith [h1, hz]
          have ha : decide ((2 : ℝ)⁻¹ < a) = false := by
            rw [decide_eq_false_iff_not]
            exact ha'
          have hrest : ∀ p ∈ l, p ≤ 1 / 2 := fun p hp => hall' p (by simp [hp])
          simpa [List.filter, ha] using ih hrest
    exact hgeneral (σ3 m hm) hall
  rw [show (σ4 m hm i).filter (fun p => decide (1 / 2 < p)) =
      [] ++ ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).filter
        (fun p => decide (1 / 2 < p)) by
    rw [σ4]
    rw [List.filter_append, hσ3]]
  have hle : (((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))).filter
      (fun p => decide (1 / 2 < p))).length ≤ i := by
    exact le_trans (List.length_filter_le (fun p => decide (1 / 2 < p))
      ((List.range i).map (fun j => fVal m (gammaVal m hm) (qVal m hm - j))))
      (by simp)
  simp [List.length_append]
  simpa [one_div] using (le_trans hle hi)

private lemma jthLargest_σ4_pos_le_b (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hjb : m - qVal m hm + i < j) : jthLargest (σ4 m hm i) j ≤ bVal m hm := by
  apply jthLargest_le_of_card_lt hj (bVal_nonneg m hm)
  rw [count_gt_b_σ4 m hm i]
  exact hjb

private lemma jthLargest_σ4_pos_le_a (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hja : 2 * m - qVal m hm + i < j) : jthLargest (σ4 m hm i) j ≤ aVal m hm := by
  apply jthLargest_le_of_card_lt hj (aVal_nonneg m hm)
  rw [count_gt_a_σ4 m hm i]
  exact hja

private lemma jthLargest_σ4_pos_le_half (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hi : i ≤ qVal m hm) (hjh : qVal m hm < j) : jthLargest (σ4 m hm i) j ≤ 1 / 2 := by
  apply jthLargest_le_of_card_lt hj (by norm_num)
  have hle := count_gt_half_σ4_le m hm i hi
  exact lt_of_le_of_lt hle hjh

/-- `(3m-q+i-1)/m = 2` for `1 <= i < q <= m`. -/
private lemma div_two_σ4 {m q i : ℕ} (hm : 4 ≤ m) (hqm : q ≤ m) (hi : 1 ≤ i) (hiq : i < q) :
    (3 * m - q + i - 1) / m = 2 := by
  rw [Nat.div_eq_of_lt_le (k := 2) (n := m) (m := 3 * m - q + i - 1)]
  · have h1 : 2 * m + (m - q) = 3 * m - q := by
      rw [← Nat.add_sub_assoc (m := m) (k := q) hqm (2 * m)]
      have hmul : 2 * m + m = 3 * m := by ring
      rw [hmul]
    have hA : 3 * m - q + i - 1 = 2 * m + (m - q + i - 1) := by
      rw [← h1]
      rw [Nat.add_assoc]
      rw [← Nat.add_sub_assoc (m := (m - q) + i) (k := 1) (by omega) (2 * m)]
    rw [hA]
    omega
  · have hle1 : (3 * m - q) + i ≤ 3 * m := by
      have h1 := Nat.add_le_add_left (by omega : i ≤ q) (3 * m - q)
      have h2 : (3 * m - q) + q = 3 * m :=
        Nat.sub_add_cancel (le_trans hqm (by omega : m ≤ 3 * m))
      rw [h2] at h1
      exact h1
    have hsub : 3 * m - q + i - 1 ≤ 3 * m - 1 := by
      exact Nat.sub_le_sub_right hle1 1
    have hlt : 3 * m - 1 < 3 * m := by omega
    omega

/-- `LB3(m, sigma4_i) <= 2b` for `i < q`. -/
lemma LB3_σ4_le_two_b (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ qVal m hm)
    (hiq : i < qVal m hm) : LB3 m (σ4 m hm i) ≤ 2 * bVal m hm := by
  classical
  have hk : ((σ4 m hm i).length - 1) / m = 2 := by
    have hlen : (σ4 m hm i).length = 3 * m - qVal m hm + i := by
      rw [σ4, List.length_append]
      rw [σ3, List.length_append]
      rw [σ2, List.length_append]
      simp [σ1]
      have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      have hcalc : m + m + (m - qVal m hm) = 3 * m - qVal m hm := by
        rw [← Nat.add_sub_assoc (m := m) (k := qVal m hm) hq_le_m (m + m)]
        have hmul : (m + m) + m = 3 * m := by ring
        rw [hmul]
      rw [hcalc]
    rw [hlen]
    have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
    exact div_two_σ4 hm hq_le_m hi hiq
  have hnon : (Finset.Icc 1 2 : Finset ℕ).Nonempty := by simp
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
  have hb_m : m - qVal m hm + i < m := by omega
  have hb_m1 : m - qVal m hm + i < m + 1 := by omega
  have hb_2m1 : m - qVal m hm + i < 2 * m - 1 := by omega
  have ha_2m : 2 * m - qVal m hm + i < 2 * m := by omega
  have ha_2m1 : 2 * m - qVal m hm + i < 2 * m + 1 := by omega
  have h1 : jthLargest (σ4 m hm i) m ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm i m (by omega) hb_m
  have h2 : jthLargest (σ4 m hm i) (m + 1) ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm i (m + 1) (by omega) hb_m1
  have h3 : jthLargest (σ4 m hm i) (2 * m - 1) ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm i (2 * m - 1) (by omega) hb_2m1
  have h4 : jthLargest (σ4 m hm i) (2 * m) ≤ aVal m hm :=
    jthLargest_σ4_pos_le_a m hm i (2 * m) (by omega) ha_2m
  have h5 : jthLargest (σ4 m hm i) (2 * m + 1) ≤ aVal m hm :=
    jthLargest_σ4_pos_le_a m hm i (2 * m + 1) (by omega) ha_2m1
  have h2a : 2 * aVal m hm ≤ bVal m hm := two_aVal_le_bVal m hm
  have hb2 : bVal m hm + 2 * aVal m hm ≤ 2 * bVal m hm := by nlinarith [h2a]
  have hf1 : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ4 m hm i) j) ≤ 2 * bVal m hm := by
    have hsum : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ4 m hm i) j) =
        jthLargest (σ4 m hm i) m + jthLargest (σ4 m hm i) (m + 1) := by
      have hIcc : Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1) = ({m, m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        omega
      rw [hIcc]
      simp
    rw [hsum]
    nlinarith [h1, h2]
  have hf2 : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ4 m hm i) j) ≤ 2 * bVal m hm := by
    have hsum : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ4 m hm i) j) =
        jthLargest (σ4 m hm i) (2 * m - 1) + jthLargest (σ4 m hm i) (2 * m) +
          jthLargest (σ4 m hm i) (2 * m + 1) := by
      have hIcc : Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1) = ({2 * m - 1, 2 * m, 2 * m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        have hnorm : m * 2 = 2 * m := by ring
        rw [hnorm]
        omega
      rw [hIcc]
      have hn1 : 2 * m - 1 ∉ ({2 * m, 2 * m + 1} : Finset ℕ) := by
        intro h
        rw [Finset.mem_insert] at h
        rw [Finset.mem_singleton] at h
        omega
      have hn2 : 2 * m ∉ ({2 * m + 1} : Finset ℕ) := by
        intro h
        rw [Finset.mem_singleton] at h
        omega
      rw [Finset.sum_insert hn1]
      rw [Finset.sum_insert hn2]
      rw [Finset.sum_singleton]
      rw [add_assoc]
    rw [hsum]
    nlinarith [h3, h4, h5, hb2]
  dsimp [LB3]
  rw [hk]
  by_cases hc : (Finset.Icc 1 2).Nonempty
  · rw [dif_pos hc]
    apply Finset.sup'_le
    intro k hk1
    have hk12 : k = 1 ∨ k = 2 := by
      rw [Finset.mem_Icc] at hk1
      omega
    rcases hk12 with rfl | rfl
    · exact hf1
    · exact hf2
  · exfalso
    exact hc hnon

/-- `f_j(gamma) <= f_{j'}(gamma)` for `j' <= j <= q`. -/
lemma fVal_le_of_ge (m : ℕ) (hm : 4 ≤ m) (j j' : ℕ) (hge : j' ≤ j) (hj : j ≤ qVal m hm) :
    fVal m (gammaVal m hm) j ≤ fVal m (gammaVal m hm) j' := by
  have hsucc : ∀ k : ℕ, fVal m (gammaVal m hm) (k + 1) ≤ fVal m (gammaVal m hm) k :=
    fVal_succ_le m hm
  have hmain : ∀ d : ℕ, ∀ j : ℕ, j' ≤ j → j - j' = d →
      fVal m (gammaVal m hm) j ≤ fVal m (gammaVal m hm) j' := by
    intro d
    induction d with
    | zero =>
        intro j hj hd
        have hjj : j = j' := by omega
        rw [hjj]
    | succ d ih =>
        intro j hj hd
        have hgt : j' < j := by omega
        have hstep : fVal m (gammaVal m hm) j ≤ fVal m (gammaVal m hm) (j - 1) := by
          have hsucc' := hsucc (j - 1)
          have hji : (j - 1) + 1 = j := by omega
          rwa [hji] at hsucc'
        have hih : fVal m (gammaVal m hm) (j - 1) ≤ fVal m (gammaVal m hm) j' := by
          have hd1 : (j - 1) - j' = d := by omega
          have hj1 : j' ≤ j - 1 := by omega
          exact ih (j - 1) hj1 hd1
        exact le_trans hstep hih
  exact hmain (j - j') j (by omega) rfl

/-- `LB3(m, sigma4_q) <= b + 1/2`. -/
lemma LB3_σ4_q_le (m : ℕ) (hm : 4 ≤ m) :
    LB3 m (σ4 m hm (qVal m hm)) ≤ bVal m hm + 1 / 2 := by
  classical
  have hk : ((σ4 m hm (qVal m hm)).length - 1) / m = 2 := by
    have hlen : (σ4 m hm (qVal m hm)).length = 3 * m := by
      rw [σ4, List.length_append]
      rw [σ3, List.length_append]
      rw [σ2, List.length_append]
      simp [σ1]
      have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      have hcalc : m + m + (m - qVal m hm) = 3 * m - qVal m hm := by
        rw [← Nat.add_sub_assoc (m := m) (k := qVal m hm) hq_le_m (m + m)]
        have hmul : (m + m) + m = 3 * m := by ring
        rw [hmul]
      rw [hcalc]
      rw [Nat.sub_add_cancel (le_trans hq_le_m (by omega : m ≤ 3 * m))]
    rw [hlen]
    rw [Nat.div_eq_of_lt_le (k := 2) (n := m) (m := 3 * m - 1)]
    · omega
    · omega
  have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  have hba : bVal m hm + aVal m hm ≤ 1 / 2 := by
    have hg : gammaVal m hm ≤ 1 := gammaVal_le_one m hm
    have hab : aVal m hm + bVal m hm = gammaVal m hm - 1 / 2 := aVal_add_bVal m hm
    have hab' : bVal m hm + aVal m hm = gammaVal m hm - 1 / 2 := by
      rw [add_comm]
      exact hab
    nlinarith [hg, hab']
  have hb2a : bVal m hm + 2 * aVal m hm ≤ bVal m hm + 1 / 2 := by
    nlinarith [hba, aVal_le_bVal m hm]
  have hqm1 : qVal m hm < m := by
    have hqt : qVal m hm ≤ tVal m := qVal_le_t m hm
    have ht : tVal m < m := by dsimp [tVal]; omega
    omega
  have h1 : jthLargest (σ4 m hm (qVal m hm)) m ≤ 1 / 2 :=
    jthLargest_σ4_pos_le_half m hm (qVal m hm) m (by omega) (le_rfl) hqm1
  have h2 : jthLargest (σ4 m hm (qVal m hm)) (m + 1) ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm (qVal m hm) (m + 1) (by omega) (by omega)
  have h3 : jthLargest (σ4 m hm (qVal m hm)) (2 * m - 1) ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm (qVal m hm) (2 * m - 1) (by omega) (by omega)
  have h4 : jthLargest (σ4 m hm (qVal m hm)) (2 * m) ≤ bVal m hm :=
    jthLargest_σ4_pos_le_b m hm (qVal m hm) (2 * m) (by omega) (by omega)
  have h5 : jthLargest (σ4 m hm (qVal m hm)) (2 * m + 1) ≤ aVal m hm :=
    jthLargest_σ4_pos_le_a m hm (qVal m hm) (2 * m + 1) (by omega) (by omega)
  have hf1 : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ4 m hm (qVal m hm)) j) ≤ bVal m hm + 1 / 2 := by
    have hsum : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ4 m hm (qVal m hm)) j) =
        jthLargest (σ4 m hm (qVal m hm)) m + jthLargest (σ4 m hm (qVal m hm)) (m + 1) := by
      have hIcc : Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1) = ({m, m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        omega
      rw [hIcc]
      simp
    rw [hsum]
    nlinarith [h1, h2]
  have hf2 : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ4 m hm (qVal m hm)) j) ≤ bVal m hm + 1 / 2 := by
    have hsum : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ4 m hm (qVal m hm)) j) =
        jthLargest (σ4 m hm (qVal m hm)) (2 * m - 1) + jthLargest (σ4 m hm (qVal m hm)) (2 * m) +
          jthLargest (σ4 m hm (qVal m hm)) (2 * m + 1) := by
      have hIcc : Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1) = ({2 * m - 1, 2 * m, 2 * m + 1} : Finset ℕ) := by
        ext j
        simp [Finset.mem_Icc]
        have hnorm : m * 2 = 2 * m := by ring
        rw [hnorm]
        omega
      rw [hIcc]
      have hn1 : 2 * m - 1 ∉ ({2 * m, 2 * m + 1} : Finset ℕ) := by
        intro h
        rw [Finset.mem_insert] at h
        rw [Finset.mem_singleton] at h
        omega
      have hn2 : 2 * m ∉ ({2 * m + 1} : Finset ℕ) := by
        intro h
        rw [Finset.mem_singleton] at h
        omega
      rw [Finset.sum_insert hn1]
      rw [Finset.sum_insert hn2]
      rw [Finset.sum_singleton]
      rw [add_assoc]
    rw [hsum]
    nlinarith [h3, h4, h5, hba]
  dsimp [LB3]
  rw [hk]
  have hnon : (Finset.Icc 1 2 : Finset ℕ).Nonempty := by simp
  by_cases hc : (Finset.Icc 1 2).Nonempty
  · rw [dif_pos hc]
    apply Finset.sup'_le
    intro k hk1
    have hk12 : k = 1 ∨ k = 2 := by
      rw [Finset.mem_Icc] at hk1
      omega
    rcases hk12 with rfl | rfl
    · exact hf1
    · exact hf2
  · exfalso
    exact hc hnon

/-- `LB2(m, sigma4_i) <= f_{q+1-i}(gamma)`. -/
lemma LB2_σ4_le (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ qVal m hm) :
    maxJobSize (σ4 m hm i) ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - i) := by
  have hf_nonneg : 0 ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - i) := by
    have hge : 1 / 2 ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - i) :=
      fVal_ge_half_of_le_q m hm (qVal m hm + 1 - i) (by omega)
    nlinarith
  apply maxJobSize_le_of_forall hf_nonneg
  intro p hp
  rcases List.mem_append.mp hp with hp2 | hp3
  · rcases List.mem_append.mp hp2 with hp2' | hp3'
    · rcases List.mem_append.mp hp2' with hp1 | hp2''
      · rcases List.mem_replicate.mp hp1 with ⟨_, rfl⟩
        have h2 : 1 / 2 ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - i) :=
          fVal_ge_half_of_le_q m hm (qVal m hm + 1 - i) (by omega)
        exact le_trans (le_trans (aVal_le_bVal m hm) (le_of_lt (bVal_lt_half m hm))) h2
      · rcases List.mem_replicate.mp hp2'' with ⟨_, rfl⟩
        have h2 : 1 / 2 ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - i) :=
          fVal_ge_half_of_le_q m hm (qVal m hm + 1 - i) (by omega)
        exact le_trans (le_of_lt (bVal_lt_half m hm)) h2
    · rcases List.mem_replicate.mp hp3' with ⟨_, rfl⟩
      exact fVal_ge_half_of_le_q m hm (qVal m hm + 1 - i) (by omega)
  · rcases List.mem_map.mp hp3 with ⟨k, hk, rfl⟩
    have hklt : k < i := List.mem_range.mp hk
    have hge : qVal m hm + 1 - i ≤ qVal m hm - k := by omega
    have hq : qVal m hm - k ≤ qVal m hm := by omega
    exact fVal_le_of_ge m hm (qVal m hm - k) (qVal m hm + 1 - i) hge hq

/-- `f_j(gamma) <= 1` for `1 <= j <= q`. -/
private lemma fVal_le_one (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ qVal m hm) :
    fVal m (gammaVal m hm) j ≤ 1 := by
  have hle1 : fVal m (gammaVal m hm) j ≤ fVal m (gammaVal m hm) 1 :=
    fVal_le_of_ge m hm j 1 hj1 hj
  have hf1 : fVal m (gammaVal m hm) 1 ≤ 1 := by
    have hc_le : cVal m (gammaVal m hm) ≤ 1 := by
      dsimp [cVal]
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hg : 0 ≤ gammaVal m hm := le_trans (by norm_num) (gammaVal_ge_five_seven m hm)
      have hnum : (m : ℝ) - 1 - gammaVal m hm ≤ (m : ℝ) := by nlinarith [hg]
      exact (div_le_one₀ hm_pos).2 hnum
    dsimp [fVal]
    exact pow_le_one₀ (le_of_lt (by
      dsimp [cVal]
      have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hg1 : gammaVal m hm < 1 := lt_of_le_of_lt (gammaVal_le_alpha m hm) (tanAlpha_lt_one)
      have hnum : 0 < (m : ℝ) - 1 - gammaVal m hm := by
        have h3 : (3 : ℝ) - gammaVal m hm > 2 := by nlinarith [hg1]
        have h4 : (m : ℝ) - 1 - gammaVal m hm ≥ (3 : ℝ) - gammaVal m hm := by nlinarith [hmr]
        nlinarith
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      exact div_pos hnum hm_pos)) hc_le
  exact le_trans hle1 hf1

/-- `PseudoLB(m, sigma4_i) <= (gamma + f_{q+1-i}(gamma))/(1 + gamma)`. -/
lemma PseudoLBGen_σ4_le (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ qVal m hm) :
    PseudoLBGen m (σ4 m hm i) ≤
      (gammaVal m hm + fVal m (gammaVal m hm) (qVal m hm + 1 - i)) / (1 + gammaVal m hm) := by
  have hlb1 := LB1_σ4_le m hm i hi hi_le
  have hlb2 := LB2_σ4_le m hm i hi hi_le
  let hf : ℝ := fVal m (gammaVal m hm) (qVal m hm + 1 - i)
  have hden : 0 < 1 + gammaVal m hm := by nlinarith [gammaVal_gt_half m hm]
  have hf_le_one : hf ≤ 1 := by
    dsimp [hf]
    exact fVal_le_one m hm (qVal m hm + 1 - i) (by omega) (by omega)
  have hf_ge_half : 1 / 2 ≤ hf := by
    dsimp [hf]
    exact fVal_ge_half_of_le_q m hm (qVal m hm + 1 - i) (by omega)
  have hb2 : hf ≤ (gammaVal m hm + hf) / (1 + gammaVal m hm) := by
    rw [le_div_iff₀ hden]
    nlinarith [hf_le_one, gammaVal_gt_half m hm]
  have hb2' : maxJobSize (σ4 m hm i) ≤ (gammaVal m hm + hf) / (1 + gammaVal m hm) :=
    le_trans hlb2 (by dsimp [hf] at hb2 ⊢; exact hb2)
  have hmid : 2 / 3 ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) := by
    rw [le_div_iff₀ hden]
    nlinarith [gammaVal_gt_half m hm]
  by_cases hiq : i < qVal m hm
  · have hb13 : 2 * bVal m hm ≤ 2 / 3 := by
      have h := gammaVal_mul_le_one_third m hm
      dsimp [bVal]
      nlinarith
    have hlb3' : LB3 m (σ4 m hm i) ≤ (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) :=
      le_trans (LB3_σ4_le_two_b m hm i hi hi_le hiq) (le_trans hb13 hmid)
    have hstep : (gammaVal m hm + 1 / 2) / (1 + gammaVal m hm) ≤
        (gammaVal m hm + hf) / (1 + gammaVal m hm) := by
      have hle' : gammaVal m hm + 1 / 2 ≤ gammaVal m hm + hf := by
        dsimp [hf]
        nlinarith [hf_ge_half]
      exact div_le_div_of_nonneg_right hle' (le_of_lt hden)
    dsimp [PseudoLBGen]
    exact max_le (le_trans hlb1 (by rfl)) (max_le hb2'
      (le_trans hlb3' hstep))
  · have hiq' : i = qVal m hm := by omega
    subst i
    have hlb3q := LB3_σ4_q_le m hm
    have hbq : bVal m hm + 1 / 2 ≤ ((m : ℝ) - 1) / (m : ℝ) := by
      have h := gammaVal_mul_le_one_half_sub m hm
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      dsimp [bVal]
      field_simp [hm_pos.ne'] at h
      field_simp [hm_pos.ne']
      nlinarith [h]
    have hqlb : ((m : ℝ) - 1) / (m : ℝ) ≤ (gammaVal m hm + hf) / (1 + gammaVal m hm) := by
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hq' : qVal m hm + 1 - qVal m hm = 1 := by omega
      have hf1 : hf = ((m : ℝ) - 1 - gammaVal m hm) / (m : ℝ) := by
        change fVal m (gammaVal m hm) (qVal m hm + 1 - qVal m hm) =
          ((m : ℝ) - 1 - gammaVal m hm) / (m : ℝ)
        rw [hq']
        exact fVal_one_gamma m hm
      field_simp [hm_pos.ne', hden.ne'] at hf1
      field_simp [hm_pos.ne', hden.ne']
      nlinarith
    have hlb3' : LB3 m (σ4 m hm (qVal m hm)) ≤ (gammaVal m hm + hf) / (1 + gammaVal m hm) :=
      le_trans hlb3q (le_trans hbq hqlb)
    dsimp [PseudoLBGen]
    exact max_le (le_trans hlb1 (by rfl)) (max_le hb2' hlb3')

/-! ### Phase 4 (continued): the phase-5 prefix -/

private lemma count_gt_b_σ5 (m : ℕ) (hm : 4 ≤ m) :
    ((σ5 m hm).filter fun p => decide (bVal m hm < p)).length = m + 1 := by
  dsimp [σ5]
  rw [List.filter_append, List.length_append]
  rw [count_gt_b_σ4 m hm (qVal m hm)]
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  rw [Nat.sub_add_cancel hq_le_m]
  have h1 : decide (bVal m hm < 1) = true := by
    rw [decide_eq_true_eq]
    exact lt_trans (bVal_lt_half m hm) (by norm_num : (1 : ℝ) / 2 < 1)
  have hf1 : ([1] : List ℝ).filter (fun p => decide (bVal m hm < p)) = [1] := by
    simp [h1]
  rw [hf1]
  simp

private lemma count_gt_a_σ5 (m : ℕ) (hm : 4 ≤ m) :
    ((σ5 m hm).filter fun p => decide (aVal m hm < p)).length = 2 * m + 1 := by
  dsimp [σ5]
  rw [List.filter_append, List.length_append]
  rw [count_gt_a_σ4 m hm (qVal m hm)]
  have hq_le_2m : qVal m hm ≤ 2 * m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  rw [Nat.sub_add_cancel hq_le_2m]
  have h1 : decide (aVal m hm < 1) = true := by
    rw [decide_eq_true_eq]
    exact lt_trans (aVal_lt_bVal m hm) (lt_trans (bVal_lt_half m hm) (by norm_num : (1 : ℝ) / 2 < 1))
  have hf1 : ([1] : List ℝ).filter (fun p => decide (aVal m hm < p)) = [1] := by
    simp [h1]
  simpa [hf1]

private lemma count_gt_half_σ5_le (m : ℕ) (hm : 4 ≤ m) :
    ((σ5 m hm).filter fun p => decide (1 / 2 < p)).length ≤ qVal m hm + 1 := by
  dsimp [σ5]
  rw [List.filter_append, List.length_append]
  have hle := count_gt_half_σ4_le m hm (qVal m hm) (le_rfl)
  have h1 : decide ((2 : ℝ)⁻¹ < 1) = true := by
    rw [decide_eq_true_eq]
    norm_num
  have hf1 : ([1] : List ℝ).filter (fun p => decide (1 / 2 < p)) = [1] := by
    simp [h1]
  rw [hf1]
  rw [show ([1] : List ℝ).length = 1 by rfl]
  omega

private lemma jthLargest_σ5_le_b (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : 1 ≤ j)
    (hjb : m + 1 < j) : jthLargest (σ5 m hm) j ≤ bVal m hm := by
  apply jthLargest_le_of_card_lt hj (bVal_nonneg m hm)
  rw [count_gt_b_σ5 m hm]
  exact hjb

private lemma jthLargest_σ5_le_a (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : 1 ≤ j)
    (hja : 2 * m + 1 < j) : jthLargest (σ5 m hm) j ≤ aVal m hm := by
  apply jthLargest_le_of_card_lt hj (aVal_nonneg m hm)
  rw [count_gt_a_σ5 m hm]
  exact hja

private lemma jthLargest_σ5_le_half (m : ℕ) (hm : 4 ≤ m) (j : ℕ) (hj : 1 ≤ j)
    (hjh : qVal m hm + 1 < j) : jthLargest (σ5 m hm) j ≤ 1 / 2 := by
  apply jthLargest_le_of_card_lt hj (by norm_num)
  have hle := count_gt_half_σ5_le m hm
  exact lt_of_le_of_lt hle hjh

/-- `PseudoLB(m, sigma5) <= 1`. -/
lemma PseudoLBGen_σ5_le_one (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ5 m hm) ≤ 1 := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  -- LB1 ≤ 1
  have hlb1 : totalLoad (σ5 m hm) / (m : ℝ) ≤ 1 := by
    have htotal : totalLoad (σ5 m hm) =
        (m : ℝ) * aVal m hm + (m : ℝ) * bVal m hm + ((m : ℝ) - (qVal m hm : ℝ)) / 2 +
          phase4Sum m hm (qVal m hm) + 1 := by
      dsimp [σ5, σ4, σ3, σ2, σ1, totalLoad]
      simp
      rw [phase4_totalLoad m hm (qVal m hm) (le_rfl)]
      have hmn : (↑(m - qVal m hm) : ℝ) = (m : ℝ) - (qVal m hm : ℝ) := by
        have hq_le : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
        exact Nat.cast_sub hq_le
      rw [hmn]
      ring
    have hmain := gammaVal_main_ineq m hm
    have hle' : totalLoad (σ5 m hm) / (m : ℝ) ≤
        gammaVal m hm - 1 / 2 + (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 +
          phase4Sum m hm (qVal m hm)) + 1 / (m : ℝ) := by
      rw [htotal]
      field_simp [hm_pos.ne']
      nlinarith [aVal_add_bVal m hm]
    have hle'' : gammaVal m hm - 1 / 2 + (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 +
          phase4Sum m hm (qVal m hm)) + 1 / (m : ℝ) ≤ 1 := by
      have hplus : gammaVal m hm - 1 / 2 + (1 / (m : ℝ)) * (((m : ℝ) - (qVal m hm : ℝ)) / 2 +
            phase4Sum m hm (qVal m hm)) + 1 / (m : ℝ) ≤
          ((m : ℝ) - 1) / (m : ℝ) + 1 / (m : ℝ) :=
        by
          have hsq : phase4Sum m hm (qVal m hm) =
              ∑ j ∈ Finset.Icc 1 (qVal m hm), fVal m (gammaVal m hm) j := by
            dsimp [phase4Sum]
            rw [show qVal m hm + 1 - qVal m hm = 1 by omega]
          rw [hsq]
          field_simp [hm_pos.ne'] at hmain
          field_simp [hm_pos.ne']
          ring_nf
          nlinarith [hmain]
      have hsum : ((m : ℝ) - 1) / (m : ℝ) + 1 / (m : ℝ) = 1 := by
        field_simp [hm_pos.ne']
        ring
      rw [hsum] at hplus
      exact hplus
    exact le_trans hle' hle''
  -- LB2 ≤ 1
  have hlb2 : maxJobSize (σ5 m hm) ≤ 1 := by
    apply maxJobSize_le_of_forall (by norm_num)
    intro p hp
    have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
    rcases List.mem_append.mp hp with hp4 | hp5
    · -- p ∈ σ4_q — ≤ f_1 ≤ 1
      have hb2 := LB2_σ4_le m hm (qVal m hm) (qVal_ge_one m hm) (le_rfl)
      have hp_le : p ≤ fVal m (gammaVal m hm) (qVal m hm + 1 - qVal m hm) :=
        le_trans (maxJobSize_ge_each (σ4 m hm (qVal m hm)) p hp4) hb2
      have hf : fVal m (gammaVal m hm) (qVal m hm + 1 - qVal m hm) ≤ 1 := by
        have hq' : qVal m hm + 1 - qVal m hm = 1 := by omega
        rw [hq']
        exact fVal_le_one m hm 1 (by omega) hq1
      exact le_trans hp_le hf
    · rcases List.mem_singleton.mp hp5 with rfl
      exact le_rfl
  -- LB3 ≤ 1
  have hb13 : 3 * bVal m hm ≤ 1 := by
    have h := gammaVal_mul_le_one_third m hm
    dsimp [bVal]
    nlinarith
  have ha4 : 4 * aVal m hm ≤ 1 := by
    have hg : (5 / 7 : ℝ) ≤ gammaVal m hm := gammaVal_ge_five_seven m hm
    have hle1 : gammaVal m hm ≤ 1 := gammaVal_le_one m hm
    dsimp [aVal]
    nlinarith
  have hk : ((σ5 m hm).length - 1) / m = 3 := by
    have hlen : (σ5 m hm).length = 3 * m + 1 := by
      rw [σ5, List.length_append]
      rw [σ4, List.length_append]
      rw [σ3, List.length_append]
      rw [σ2, List.length_append]
      simp [σ1]
      have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
      have hcalc : m + m + (m - qVal m hm) = 3 * m - qVal m hm := by
        rw [← Nat.add_sub_assoc (m := m) (k := qVal m hm) hq_le_m (m + m)]
        have hmul : (m + m) + m = 3 * m := by ring
        rw [hmul]
      rw [hcalc]
      rw [Nat.sub_add_cancel (le_trans hq_le_m (by omega : m ≤ 3 * m))]
    rw [hlen]
    rw [Nat.add_sub_cancel]
    rw [Nat.div_eq_of_lt_le (k := 3) (n := m) (m := 3 * m)]
    · omega
    · omega
  have hnon : (Finset.Icc 1 3 : Finset ℕ).Nonempty := by simp
  have hlb3 : LB3 m (σ5 m hm) ≤ 1 := by
    have hq1 : 1 ≤ qVal m hm := qVal_ge_one m hm
    have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
    have hqt1 : qVal m hm + 1 < m := by
      have hqt : qVal m hm ≤ tVal m := qVal_le_t m hm
      have ht : tVal m + 1 < m := by dsimp [tVal]; omega
      omega
    have hqt2 : qVal m hm + 1 < m + 1 := by omega
    have h1a : jthLargest (σ5 m hm) m ≤ 1 / 2 :=
      jthLargest_σ5_le_half m hm m (by omega) hqt1
    have h1b : jthLargest (σ5 m hm) (m + 1) ≤ 1 / 2 :=
      jthLargest_σ5_le_half m hm (m + 1) (by omega) hqt2
    have h2a : jthLargest (σ5 m hm) (2 * m - 1) ≤ bVal m hm :=
      jthLargest_σ5_le_b m hm (2 * m - 1) (by omega) (by omega)
    have h2b : jthLargest (σ5 m hm) (2 * m) ≤ bVal m hm :=
      jthLargest_σ5_le_b m hm (2 * m) (by omega) (by omega)
    have h2c : jthLargest (σ5 m hm) (2 * m + 1) ≤ bVal m hm :=
      jthLargest_σ5_le_b m hm (2 * m + 1) (by omega) (by omega)
    have h3a : jthLargest (σ5 m hm) (3 * m - 2) ≤ aVal m hm :=
      jthLargest_σ5_le_a m hm (3 * m - 2) (by omega) (by omega)
    have h3b : jthLargest (σ5 m hm) (3 * m - 1) ≤ aVal m hm :=
      jthLargest_σ5_le_a m hm (3 * m - 1) (by omega) (by omega)
    have h3c : jthLargest (σ5 m hm) (3 * m) ≤ aVal m hm :=
      jthLargest_σ5_le_a m hm (3 * m) (by omega) (by omega)
    have h3d : jthLargest (σ5 m hm) (3 * m + 1) ≤ aVal m hm :=
      jthLargest_σ5_le_a m hm (3 * m + 1) (by omega) (by omega)
    dsimp [LB3]
    rw [hk]
    by_cases hc : (Finset.Icc 1 3).Nonempty
    · rw [dif_pos hc]
      apply Finset.sup'_le
      intro k hk1
      have hk13 : k = 1 ∨ k = 2 ∨ k = 3 := by
        rw [Finset.mem_Icc] at hk1
        omega
      rcases hk13 with rfl | rfl | rfl
      · -- k=1: positions m, m+1 — both ≤ 1/2
        have hsum : (∑ j ∈ Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1), jthLargest (σ5 m hm) j) =
            jthLargest (σ5 m hm) m + jthLargest (σ5 m hm) (m + 1) := by
          have hIcc : Finset.Icc (m * 1 - 1 + 1) (m * 1 + 1) = ({m, m + 1} : Finset ℕ) := by
            ext j
            simp [Finset.mem_Icc]
            omega
          rw [hIcc]
          simp
        rw [hsum]
        nlinarith [h1a, h1b]
      · -- k=2: three terms ≤ b
        have hsum : (∑ j ∈ Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1), jthLargest (σ5 m hm) j) =
            jthLargest (σ5 m hm) (2 * m - 1) + jthLargest (σ5 m hm) (2 * m) +
              jthLargest (σ5 m hm) (2 * m + 1) := by
          have hIcc : Finset.Icc (m * 2 - 2 + 1) (m * 2 + 1) = ({2 * m - 1, 2 * m, 2 * m + 1} : Finset ℕ) := by
            ext j
            simp [Finset.mem_Icc]
            have hnorm : m * 2 = 2 * m := by ring
            rw [hnorm]
            omega
          rw [hIcc]
          have hn1 : 2 * m - 1 ∉ ({2 * m, 2 * m + 1} : Finset ℕ) := by
            intro h
            rw [Finset.mem_insert] at h
            rw [Finset.mem_singleton] at h
            omega
          have hn2 : 2 * m ∉ ({2 * m + 1} : Finset ℕ) := by
            intro h
            rw [Finset.mem_singleton] at h
            omega
          rw [Finset.sum_insert hn1]
          rw [Finset.sum_insert hn2]
          rw [Finset.sum_singleton]
          rw [add_assoc]
        rw [hsum]
        nlinarith [h2a, h2b, h2c, hb13]
      · -- k=3: four terms ≤ a
        have hsum : (∑ j ∈ Finset.Icc (m * 3 - 3 + 1) (m * 3 + 1), jthLargest (σ5 m hm) j) =
            jthLargest (σ5 m hm) (3 * m - 2) + jthLargest (σ5 m hm) (3 * m - 1) +
              jthLargest (σ5 m hm) (3 * m) + jthLargest (σ5 m hm) (3 * m + 1) := by
          have hIcc : Finset.Icc (m * 3 - 3 + 1) (m * 3 + 1) =
              ({3 * m - 2, 3 * m - 1, 3 * m, 3 * m + 1} : Finset ℕ) := by
            ext j
            simp [Finset.mem_Icc]
            have hnorm : m * 3 = 3 * m := by ring
            rw [hnorm]
            omega
          rw [hIcc]
          have hn1 : 3 * m - 2 ∉ ({3 * m - 1, 3 * m, 3 * m + 1} : Finset ℕ) := by
            intro h
            rw [Finset.mem_insert] at h
            rw [Finset.mem_insert] at h
            rw [Finset.mem_singleton] at h
            omega
          have hn2 : 3 * m - 1 ∉ ({3 * m, 3 * m + 1} : Finset ℕ) := by
            intro h
            rw [Finset.mem_insert] at h
            rw [Finset.mem_singleton] at h
            omega
          have hn3 : 3 * m ∉ ({3 * m + 1} : Finset ℕ) := by
            intro h
            rw [Finset.mem_singleton] at h
            omega
          rw [Finset.sum_insert hn1]
          rw [Finset.sum_insert hn2]
          rw [Finset.sum_insert hn3]
          rw [Finset.sum_singleton]
          rw [add_assoc, add_assoc]
        rw [hsum]
        nlinarith [h3a, h3b, h3c, h3d, ha4]
    · exfalso
      exact hc hnon
  dsimp [PseudoLBGen]
  exact max_le hlb1 (max_le hlb2 hlb3)

/-! ### Phase 5: machine-level adversary (Theorem 3.1) -/

/-- `a_m > 0`. -/
private lemma aVal_pos (m : ℕ) (hm : 4 ≤ m) : 0 < aVal m hm := by
  have hg1 : gammaVal m hm < 1 := lt_of_le_of_lt (gammaVal_le_alpha m hm) tanAlpha_lt_one
  have h1 : 0 < 1 - gammaVal m hm := by nlinarith
  have h2 : 0 < gammaVal m hm - 1 / 2 := by nlinarith [gammaVal_gt_half m hm]
  dsimp [aVal]
  exact mul_pos h1 h2

/-- `b_m > 0`. -/
private lemma bVal_pos (m : ℕ) (hm : 4 ≤ m) : 0 < bVal m hm := by
  have hg0 : 0 < gammaVal m hm := by nlinarith [gammaVal_ge_five_seven m hm]
  have hg2 : 0 < gammaVal m hm - 1 / 2 := by nlinarith [gammaVal_gt_half m hm]
  dsimp [bVal]
  exact mul_pos hg0 hg2

/-- `1 + gamma_m > 0`. -/
private lemma one_add_gammaVal_pos (m : ℕ) (hm : 4 ≤ m) : 0 < 1 + gammaVal m hm := by
  have hg : 5 / 7 ≤ gammaVal m hm := gammaVal_ge_five_seven m hm
  nlinarith

/-- Invariant during phases 3-4: after `t` jobs of size `>= 1/2` have been placed from a
    uniform `gamma - 1/2` base, each machine has at most one such job (`n i <= 1`), exactly
    `t` machines have one, machines without one have load exactly `gamma - 1/2`, and machines
    with one have load at least `gamma`. -/
def Phase34Inv (m : ℕ) (hm : 4 ≤ m) (loads : Loads m) (n : Fin m → ℕ) (t : ℕ) : Prop :=
  (∀ i, n i ≤ 1) ∧ (∑ i, n i = t) ∧
  (∀ i, n i = 0 → loads i = gammaVal m hm - 1 / 2) ∧
  (∀ i, n i = 1 → gammaVal m hm ≤ loads i)

/-- One phase-3/4 job of size `p >= 1/2`: either the chosen machine already had a
    phase-3/4 job (collision, so the makespan is at least `gamma + p`), or the invariant
    is preserved with one more machine marked. -/
private lemma phase34_step {m : ℕ} [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m)
    (loads : Loads m) (n : Fin m → ℕ) (t : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p)
    (hinv : Phase34Inv m hm loads n t) :
    let j := alg loads p
    let loads' := step (m := m) alg loads p
    gammaVal m hm + p ≤ makespan m loads'
    ∨ ∃ n' : Fin m → ℕ, Phase34Inv m hm loads' n' (t + 1) := by
  intro j loads'
  have hj_def : j = alg loads p := rfl
  by_cases hj : n j = 0
  · right
    let n' : Fin m → ℕ := Function.update n j 1
    refine ⟨n', ?_⟩
    unfold Phase34Inv
    constructor
    · intro i
      by_cases hij : i = j
      · subst i
        simp [n', Function.update]
      · simp [n', Function.update, hij, hinv.1 i]
    · constructor
      · have hsum' : (∑ i : Fin m, n' i) = (∑ i : Fin m, n i) + 1 := by
          dsimp [n']
          calc
            (∑ i : Fin m, Function.update n j 1 i) =
                (∑ i : Fin m, if i = j then 1 else n i) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hiji : i = j
                  · subst i
                    simp [Function.update]
                  · simp [Function.update, hiji]
            _ = (∑ i : Fin m, if i = j then 1 else 0) +
                (∑ i : Fin m, if i = j then 0 else n i) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hiji : i = j
                  · subst i
                    simp
                  · simp [hiji]
            _ = 1 + (∑ i : Fin m, if i = j then 0 else n i) := by
                  rw [Finset.sum_ite_eq' (s := Finset.univ) (a := j)
                    (b := fun _ : Fin m => (1 : ℕ))]
                  simp
            _ = (∑ i : Fin m, n i) + 1 := by
                  have hsum : (∑ i : Fin m, if i = j then 0 else n i) = (∑ i : Fin m, n i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    by_cases hiji : i = j
                    · subst i
                      simp [hj]
                    · simp [hiji]
                  rw [hsum]
                  omega
        rw [hsum', hinv.2.1]
      · constructor
        · intro i hi0
          by_cases hij : i = j
          · subst i
            simp [n', Function.update] at hi0
          · have hni : n i = 0 := by
              simpa [n', Function.update, hij] using hi0
            have hstepi : loads' i = loads i := by
              dsimp [loads', step]
              simp [← hj_def, hij]
            rw [hstepi]
            exact hinv.2.2.1 i hni
        · intro i hi1
          by_cases hij : i = j
          · subst i
            have hloadj : loads j = gammaVal m hm - 1 / 2 := hinv.2.2.1 j hj
            have hstepj : loads' j = gammaVal m hm - 1 / 2 + p := by
              have hstep : loads' j = loads j + p := by
                dsimp [loads', step]
                simp [← hj_def]
              rw [hstep, hloadj]
            rw [hstepj]
            nlinarith [hp]
          · have hni : n i = 1 := by
              simpa [n', Function.update, hij] using hi1
            have hstepi : loads' i = loads i := by
              dsimp [loads', step]
              simp [← hj_def, hij]
            rw [hstepi]
            exact hinv.2.2.2 i hni
  · left
    have hn1 : n j = 1 := by
      have hle : n j ≤ 1 := hinv.1 j
      omega
    have hge : gammaVal m hm ≤ loads j := hinv.2.2.2 j hn1
    have hstepj : loads' j = loads j + p := by
      dsimp [loads', step]
      simp [← hj_def]
    have h := makespan_ge_each (m := m) loads' j
    nlinarith [hge, hstepj, h]

/-- `sigma4 (i+1) = sigma4 i ++ [f_{q-i}]`, i.e. appending the `(i+1)`-th phase-4 job. -/
private lemma σ4_succ_append (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : i < qVal m hm) :
    σ4 m hm (i + 1) = σ4 m hm i ++ [fVal m (gammaVal m hm) (qVal m hm - i)] := by
  dsimp [σ4]
  rw [List.range_succ]
  rw [List.map_append]
  simp [List.append_assoc]

/-- Phase 3: `m-q` jobs of size `1/2` are placed from a uniform `gamma - 1/2` base.
    Either a collision certifies the lower bound for `sigma3`, or after all of them the
    invariant holds with `m-q` machines marked. -/
private lemma phase3_loop {m : ℕ} [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m)
    (loads0 : Loads m) (n0 : Fin m → ℕ)
    (hinv0 : Phase34Inv m hm loads0 n0 0)
    (hrun0 : runAlgorithm m alg (σ2 m hm) = loads0) :
    (∃ sigma : JobSequence,
        (1 + gammaVal m hm) * PseudoLBGen m sigma ≤ algorithmMakespan m alg sigma) ∨
    ∃ loads : Loads m, ∃ n : Fin m → ℕ,
      Phase34Inv m hm loads n (m - qVal m hm) ∧
      runAlgorithm m alg (σ3 m hm) = loads := by
  have hmain : ∀ r : ℕ, r ≤ m - qVal m hm →
      ∀ loads : Loads m, ∀ n : Fin m → ℕ,
        Phase34Inv m hm loads n (m - qVal m hm - r) →
        runAlgorithm m alg (σ2 m hm ++ List.replicate (m - qVal m hm - r) (1 / 2)) = loads →
        (∃ sigma : JobSequence,
          (1 + gammaVal m hm) * PseudoLBGen m sigma ≤ algorithmMakespan m alg sigma) ∨
        ∃ loads' : Loads m, ∃ n' : Fin m → ℕ,
          Phase34Inv m hm loads' n' (m - qVal m hm) ∧
          runAlgorithm m alg (σ3 m hm) = loads' := by
    intro r hr
    induction r with
    | zero =>
        intro loads n hinv hrun
        right
        refine ⟨loads, n, ?_, ?_⟩
        · simpa using hinv
        · simpa [σ3] using hrun
    | succ r ih =>
        intro loads n hinv hrun
        by_cases hdone : m - qVal m hm - (r + 1) = m - qVal m hm
        · right
          refine ⟨loads, n, ?_, ?_⟩
          · simpa [hdone] using hinv
          · simpa [hdone, σ3] using hrun
        · let t := m - qVal m hm - (r + 1)
          let loads' := step (m := m) alg loads (1 / 2)
          have hstep := phase34_step (m := m) hm alg loads n t (1 / 2) (by norm_num) hinv
          rcases hstep with hcoll | hcont
          · -- collision: witness σ3
            left
            use σ3 m hm
            have hlb3 : (1 + gammaVal m hm) * PseudoLBGen m (σ3 m hm) ≤
                gammaVal m hm + 1 / 2 := by
              have hle := PseudoLBGen_σ3_le m hm
              have hne : 1 + gammaVal m hm ≠ 0 := (one_add_gammaVal_pos m hm).ne'
              have h1 : (1 + gammaVal m hm) *
                  ((gammaVal m hm + 1 / 2) / (1 + gammaVal m hm)) =
                  gammaVal m hm + 1 / 2 := by
                field_simp [hne]
              nlinarith [hle, h1, one_add_gammaVal_pos m hm]
            have hpre : gammaVal m hm + 1 / 2 ≤
                algorithmMakespan m alg (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) := by
              have hrun' : runAlgorithm m alg (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) =
                  loads' := by
                rw [List.replicate_succ', ← List.append_assoc]
                rw [runAlgorithm_append_singleton (m := m) alg
                  (σ2 m hm ++ List.replicate t (1 / 2)) (1 / 2)]
                rw [hrun]
              dsimp [algorithmMakespan]
              rw [hrun']
              exact hcoll
            have hmono : algorithmMakespan m alg (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) ≤
                algorithmMakespan m alg (σ3 m hm) := by
              have hrest : (t + 1) + (m - qVal m hm - (t + 1)) = m - qVal m hm := by omega
              have hrep2 : List.replicate (m - qVal m hm) (1 / 2 : ℝ) =
                  List.replicate (t + 1) (1 / 2 : ℝ) ++
                    List.replicate (m - qVal m hm - (t + 1)) (1 / 2 : ℝ) := by
                calc
                  List.replicate (m - qVal m hm) (1 / 2 : ℝ)
                      = List.replicate ((t + 1) + (m - qVal m hm - (t + 1))) (1 / 2 : ℝ) := by
                        congr 1
                        omega
                  _ = List.replicate (t + 1) (1 / 2 : ℝ) ++
                      List.replicate (m - qVal m hm - (t + 1)) (1 / 2 : ℝ) := by
                        exact List.replicate_add (t + 1) (m - qVal m hm - (t + 1)) (1 / 2 : ℝ)
              have hmono' := algorithmMakespan_mono (m := m) alg
                (σ2 m hm ++ List.replicate (t + 1) (1 / 2))
                (List.replicate (m - qVal m hm - (t + 1)) (1 / 2))
                (by
                  intro p hp
                  rcases List.mem_replicate.mp hp with ⟨_, rfl⟩
                  norm_num)
              have hseq : (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) ++
                  List.replicate (m - qVal m hm - (t + 1)) (1 / 2) = σ3 m hm := by
                calc
                  (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) ++
                      List.replicate (m - qVal m hm - (t + 1)) (1 / 2)
                      = σ2 m hm ++ (List.replicate (t + 1) (1 / 2) ++
                          List.replicate (m - qVal m hm - (t + 1)) (1 / 2)) := by
                        rw [List.append_assoc]
                  _ = σ2 m hm ++ List.replicate (m - qVal m hm) (1 / 2) := by
                        congr 1
                        exact hrep2.symm
                  _ = σ3 m hm := by rfl
              rw [hseq] at hmono'
              exact hmono'
            exact (calc
              (1 + gammaVal m hm) * PseudoLBGen m (σ3 m hm) ≤ gammaVal m hm + 1 / 2 := hlb3
              _ ≤ algorithmMakespan m alg (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) := hpre
              _ ≤ algorithmMakespan m alg (σ3 m hm) := hmono)
          · -- no collision: continue
            rcases hcont with ⟨n', hinv'⟩
            have hrun' : runAlgorithm m alg (σ2 m hm ++ List.replicate (t + 1) (1 / 2)) =
                loads' := by
              rw [List.replicate_succ', ← List.append_assoc]
              rw [runAlgorithm_append_singleton (m := m) alg
                (σ2 m hm ++ List.replicate t (1 / 2)) (1 / 2)]
              rw [hrun]
            have ht1 : t + 1 = m - qVal m hm - r := by omega
            have hr' : r ≤ m - qVal m hm := by omega
            exact ih hr' loads' n' (by simpa [ht1, loads'] using hinv') (by simpa [ht1] using hrun')
  exact hmain (m - qVal m hm) (le_rfl) loads0 n0 (by simpa using hinv0) (by simpa using hrun0)

/-- Phase 4: the `q` jobs `f_q(gamma), ..., f_1(gamma)` are placed on machines without a
    phase-3/4 job. Either a collision certifies the lower bound for some `sigma4 i`, or after
    all of them the invariant holds with sum `m`. -/
private lemma phase4_loop {m : ℕ} [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m)
    (loads0 : Loads m) (n0 : Fin m → ℕ)
    (hinv0 : Phase34Inv m hm loads0 n0 (m - qVal m hm))
    (hrun0 : runAlgorithm m alg (σ3 m hm) = loads0) :
    (∃ sigma : JobSequence,
        (1 + gammaVal m hm) * PseudoLBGen m sigma ≤ algorithmMakespan m alg sigma) ∨
    ∃ loads : Loads m, ∃ n : Fin m → ℕ,
      Phase34Inv m hm loads n m ∧
      runAlgorithm m alg (σ4 m hm (qVal m hm)) = loads := by
  have hq_le_m : qVal m hm ≤ m := le_trans (qVal_le_t m hm) (by dsimp [tVal]; omega)
  have hsum_m : m - qVal m hm + qVal m hm = m := by omega
  have hmain : ∀ r : ℕ, r ≤ qVal m hm →
      ∀ loads : Loads m, ∀ n : Fin m → ℕ,
        Phase34Inv m hm loads n (m - qVal m hm + (qVal m hm - r)) →
        runAlgorithm m alg (σ4 m hm (qVal m hm - r)) = loads →
        (∃ sigma : JobSequence,
          (1 + gammaVal m hm) * PseudoLBGen m sigma ≤ algorithmMakespan m alg sigma) ∨
        ∃ loads' : Loads m, ∃ n' : Fin m → ℕ,
          Phase34Inv m hm loads' n' m ∧
          runAlgorithm m alg (σ4 m hm (qVal m hm)) = loads' := by
    intro r hr
    induction r with
    | zero =>
        intro loads n hinv hrun
        right
        refine ⟨loads, n, ?_, ?_⟩
        · simpa [hsum_m] using hinv
        · simpa using hrun
    | succ r ih =>
        intro loads n hinv hrun
        by_cases hdone : qVal m hm - (r + 1) = qVal m hm
        · right
          refine ⟨loads, n, ?_, ?_⟩
          · simpa [hdone, hsum_m] using hinv
          · simpa [hdone] using hrun
        · let t := m - qVal m hm + (qVal m hm - (r + 1))
          let p := fVal m (gammaVal m hm) (r + 1)
          let loads' := step (m := m) alg loads p
          have hf : 1 / 2 ≤ p := by
            dsimp [p]
            exact fVal_ge_half_of_le_q m hm (r + 1) (by omega)
          have hstep := phase34_step (m := m) hm alg loads n t p hf hinv
          rcases hstep with hcoll | hcont
          · -- collision: witness σ4 (q-r)
            left
            use σ4 m hm (qVal m hm - r)
            have hσ4 : σ4 m hm (qVal m hm - r) =
                σ4 m hm (qVal m hm - (r + 1)) ++ [fVal m (gammaVal m hm) (r + 1)] := by
              have hi : qVal m hm - (r + 1) + 1 = qVal m hm - r := by omega
              rw [← hi]
              rw [σ4_succ_append m hm (qVal m hm - (r + 1)) (by omega)]
              congr 1
              have hss : qVal m hm - (qVal m hm - (r + 1)) = r + 1 := by
                exact Nat.sub_sub_self (by omega : r + 1 ≤ qVal m hm)
              rw [hss]
            have hpre : gammaVal m hm + p ≤
                algorithmMakespan m alg (σ4 m hm (qVal m hm - r)) := by
              have hrun' : runAlgorithm m alg (σ4 m hm (qVal m hm - r)) = loads' := by
                rw [hσ4]
                rw [runAlgorithm_append_singleton (m := m) alg
                  (σ4 m hm (qVal m hm - (r + 1))) p]
                rw [hrun]
              dsimp [algorithmMakespan]
              rw [hrun']
              exact hcoll
            have hlb4 : (1 + gammaVal m hm) * PseudoLBGen m (σ4 m hm (qVal m hm - r)) ≤
                gammaVal m hm + fVal m (gammaVal m hm) (r + 1) := by
              have h1 : 1 ≤ qVal m hm - r := by omega
              have h2 : qVal m hm - r ≤ qVal m hm := by omega
              have hle := PseudoLBGen_σ4_le m hm (qVal m hm - r) h1 h2
              have hfidx : fVal m (gammaVal m hm) (qVal m hm + 1 - (qVal m hm - r)) =
                  fVal m (gammaVal m hm) (r + 1) := by
                congr 1
                omega
              have hne : 1 + gammaVal m hm ≠ 0 := (one_add_gammaVal_pos m hm).ne'
              have hprod : (1 + gammaVal m hm) *
                  ((gammaVal m hm + fVal m (gammaVal m hm) (qVal m hm + 1 - (qVal m hm - r))) /
                    (1 + gammaVal m hm)) =
                  gammaVal m hm + fVal m (gammaVal m hm) (qVal m hm + 1 - (qVal m hm - r)) := by
                field_simp [hne]
              rw [hfidx] at hle hprod
              nlinarith [hle, hprod, one_add_gammaVal_pos m hm]
            exact (calc
              (1 + gammaVal m hm) * PseudoLBGen m (σ4 m hm (qVal m hm - r)) ≤
                  gammaVal m hm + fVal m (gammaVal m hm) (r + 1) := hlb4
              _ ≤ algorithmMakespan m alg (σ4 m hm (qVal m hm - r)) := by simpa [p] using hpre)
          · -- no collision: continue
            rcases hcont with ⟨n', hinv'⟩
            have hσ4 : σ4 m hm (qVal m hm - r) =
                σ4 m hm (qVal m hm - (r + 1)) ++ [fVal m (gammaVal m hm) (r + 1)] := by
              have hi : qVal m hm - (r + 1) + 1 = qVal m hm - r := by omega
              rw [← hi]
              rw [σ4_succ_append m hm (qVal m hm - (r + 1)) (by omega)]
              congr 1
              have hss : qVal m hm - (qVal m hm - (r + 1)) = r + 1 := by
                exact Nat.sub_sub_self (by omega : r + 1 ≤ qVal m hm)
              rw [hss]
            have hrun' : runAlgorithm m alg (σ4 m hm (qVal m hm - r)) = loads' := by
              rw [hσ4]
              rw [runAlgorithm_append_singleton (m := m) alg
                (σ4 m hm (qVal m hm - (r + 1))) p]
              rw [hrun]
            have ht1 : m - qVal m hm + (qVal m hm - r) = t + 1 := by omega
            have hr' : r ≤ qVal m hm := by omega
            exact ih hr' loads' n' (by simpa [ht1, loads'] using hinv') hrun'
  exact hmain (qVal m hm) (le_rfl) loads0 n0 (by simpa using hinv0) (by simpa [σ4] using hrun0)

/-- Theorem 3.1: for every online algorithm on `m >= 4` machines there is a job sequence
    whose makespan is at least `(1 + gamma_m)` times the pseudo lower bound. -/
theorem pseudo_lower_bound_general [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m) :
    ∃ sigma : JobSequence,
      algorithmMakespan m alg sigma ≥ (1 + gammaVal m hm) * PseudoLBGen m sigma := by
  -- Phase 1: m jobs of size a
  have h_layer1 := layer_separation (m := m) alg (aVal m hm) (aVal_pos m hm)
  rcases h_layer1 with h_imbal1 | h_bal1
  · use σ1 m hm
    have h_opt1 : OPT (σ1 m hm) = aVal m hm := by
      simpa [σ1] using opt_of_identical_jobs (m := m) (aVal m hm) (aVal_pos m hm)
    have h_two : (1 + gammaVal m hm) * aVal m hm ≤ 2 * aVal m hm := by
      nlinarith [gammaVal_le_one m hm, aVal_nonneg m hm]
    calc
      (1 + gammaVal m hm) * PseudoLBGen m (σ1 m hm) =
          (1 + gammaVal m hm) * aVal m hm := by rw [PseudoLBGen_σ1 m hm]
      _ ≤ 2 * aVal m hm := h_two
      _ = 2 * OPT (σ1 m hm) := by rw [h_opt1]
      _ ≤ algorithmMakespan m alg (σ1 m hm) := by simpa [σ1] using h_imbal1
  · -- Phase 2: m jobs of size b on base a
    have h_bal1' : ∀ i : Fin m, runAlgorithm m alg (σ1 m hm) i = aVal m hm := by
      simpa [σ1] using h_bal1
    have h_layer2 := layer_separation_from_base (m := m) alg (aVal m hm) (bVal m hm)
      (bVal_pos m hm) (runAlgorithm m alg (σ1 m hm)) h_bal1'
    rcases h_layer2 with h_imbal2 | h_bal2
    · use σ2 m hm
      have h_run2 : runAlgorithm m alg (σ2 m hm) =
          (List.replicate m (bVal m hm)).foldl (step (m := m) alg) (runAlgorithm m alg (σ1 m hm)) := by
        simp [σ2, σ1, runAlgorithm]
      have h_mk : aVal m hm + 2 * bVal m hm ≤ algorithmMakespan m alg (σ2 m hm) := by
        dsimp [algorithmMakespan]
        rw [h_run2]
        exact h_imbal2
      calc
        (1 + gammaVal m hm) * PseudoLBGen m (σ2 m hm) =
            (1 + gammaVal m hm) * (gammaVal m hm - 1 / 2) := by rw [PseudoLBGen_σ2 m hm]
        _ = aVal m hm + 2 * bVal m hm := (aVal_add_two_bVal m hm).symm
        _ ≤ algorithmMakespan m alg (σ2 m hm) := h_mk
    · -- Phases 3-5
      have h_loads2 : ∀ i : Fin m, runAlgorithm m alg (σ2 m hm) i = gammaVal m hm - 1 / 2 := by
        intro i
        have h_run2 : runAlgorithm m alg (σ2 m hm) =
            (List.replicate m (bVal m hm)).foldl (step (m := m) alg) (runAlgorithm m alg (σ1 m hm)) := by
          simp [σ2, σ1, runAlgorithm]
        rw [h_run2]
        have hi := h_bal2 i
        rw [hi]
        exact aVal_add_bVal m hm
      let loads0 : Loads m := runAlgorithm m alg (σ2 m hm)
      let n0 : Fin m → ℕ := fun _ => 0
      have hinv0 : Phase34Inv m hm loads0 n0 0 := by
        unfold Phase34Inv
        constructor
        · intro i
          simp [n0]
        · constructor
          · simp [n0]
          · constructor
            · intro i hi
              have hload := h_loads2 i
              simpa [loads0, n0] using hload
            · intro i hi
              simp [n0] at hi
      have hrun0 : runAlgorithm m alg (σ2 m hm) = loads0 := rfl
      have hloop3 := phase3_loop (m := m) hm alg loads0 n0 hinv0 hrun0
      rcases hloop3 with ⟨sigma, hcert⟩ | ⟨loads3, n3, hinv3, hrun3⟩
      · exact ⟨sigma, hcert⟩
      · have hloop4 := phase4_loop (m := m) hm alg loads3 n3 hinv3 hrun3
        rcases hloop4 with ⟨sigma, hcert⟩ | ⟨loads4, n4, hinv4, hrun4⟩
        · exact ⟨sigma, hcert⟩
        · -- Phase 5: one job of size 1
          let j := alg loads4 (1 : ℝ)
          let loads5 := step (m := m) alg loads4 (1 : ℝ)
          use σ5 m hm
          have h_all_ge : ∀ i : Fin m, gammaVal m hm ≤ loads4 i := by
            intro i
            have hn1 : n4 i = 1 := pigeonhole_all_ones (m := m) n4 hinv4.1 hinv4.2.1 i
            exact hinv4.2.2.2 i hn1
          have hrun5 : runAlgorithm m alg (σ5 m hm) = loads5 := by
            dsimp [σ5]
            rw [runAlgorithm_append_singleton (m := m) alg (σ4 m hm (qVal m hm)) (1 : ℝ)]
            dsimp [loads5]
            rw [hrun4]
          have h_mk : gammaVal m hm + 1 ≤ algorithmMakespan m alg (σ5 m hm) := by
            dsimp [algorithmMakespan]
            rw [hrun5]
            have hload : gammaVal m hm ≤ loads4 j := h_all_ge j
            have hstepj : loads5 j = loads4 j + 1 := by
              dsimp [loads5, step]
              simp [j]
            have h := makespan_ge_each (m := m) loads5 j
            nlinarith [hload, hstepj, h]
          have hlb5 : (1 + gammaVal m hm) * PseudoLBGen m (σ5 m hm) ≤ gammaVal m hm + 1 := by
            have hle := PseudoLBGen_σ5_le_one m hm
            nlinarith [hle, one_add_gammaVal_pos m hm]
          exact (calc
            (1 + gammaVal m hm) * PseudoLBGen m (σ5 m hm) ≤ gammaVal m hm + 1 := hlb5
            _ ≤ algorithmMakespan m alg (σ5 m hm) := h_mk)

end OnlineScheduling
