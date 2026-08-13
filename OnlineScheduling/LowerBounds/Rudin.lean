/-
Rudin's Lower Bounds (SIAM J. Comput. 32(3):717-735, 2003)
m=4: sqrt(3) ≈ 1.732 via mixed type-1/type-2 layers (Theorem 3.1)
Asymptotic: 1.88 for m ≥ 3454

Formalization of Section 3 (four machines, Theorem 3.1).

Parameters (ε, with `rudinOK eps`):
  V = √3 − 1 − ε   (so 1 + V = √3 − ε)
  M = (3V − 2) / 2
  S₀ = 1, A₀ = 1/(2V), B₀ = 1 − A₀ − M·A₀ (= 1/4)
  S_{i+1} = M·A_i,  A_{i+1} = (A_i − 2B_i)/4
  B_{i+1} = S_{i+1} − A_{i+1} − M·A_{i+1}  while R_{i+1} := A_{i+1}/S_{i+1} < V,
          = S_{i+1} − A_{i+1}            otherwise (final layer)
The recurrence terminates (Lemma 3.2: the ratio R_i grows exponentially),
each layer must be split among the four machines (Lemma 3.4), the prefix
admits a packing of makespan ≤ 2A₀ (Lemma 3.3), and the final job 2A₀
forces the ratio 1 + V (Lemma 3.5).
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

namespace OnlineScheduling

noncomputable section

def rudin_asymptotic : ℝ := 1.88

private lemma rudin_foldl_max_ge_acc (a : ℝ) (σ : List ℝ) :
    a ≤ List.foldl max a σ := by
  induction σ generalizing a with
  | nil => simp
  | cons p σ ih =>
      simp [List.foldl]
      exact le_trans (le_max_left a p) (ih (max a p))

private lemma rudin_opt_nonneg (σ : JobSequence) : 0 ≤ OPT σ := by
  exact le_trans (rudin_foldl_max_ge_acc (0 : ℝ) σ) (opt_ge_max_job σ)

/-- For two distinct machines j ≠ j0, exactly two of the four indices are
    neither j nor j0, so the indicator sum equals 2. -/
private lemma rudin_sum_indicator_two (j j0 : Fin 4) (hne : j ≠ j0) :
    (∑ x : Fin 4, (if x = j ∨ x = j0 then 0 else 1 : ℕ)) = 2 := by
  fin_cases j <;> fin_cases j0 <;> simp [Fin.sum_univ_four] at hne ⊢

/-- Rudin recurrence for Type-2 layer ratio evolution.
    R_{i+1} = f(R_i), M = (3V-2)/2. -/
noncomputable def rudin_R_step (V R_prev : ℝ) : ℝ :=
  let M := (3 * V - 2) / 2
  3 / (4 * M) + 1 / 2 - 1 / (2 * M * R_prev)

/-! ### Parameterized construction (Section 3) -/

/-- V = √3 − 1 − ε, so 1 + V = √3 − ε. -/
def rudinV (eps : ℝ) : ℝ := Real.sqrt 3 - 1 - eps

/-- M = (3V − 2)/2. -/
def rudinM (eps : ℝ) : ℝ := (3 * rudinV eps - 2) / 2

/-- The parameter ε must be positive and safely small (0 < ε < 1/100). -/
def rudinOK (eps : ℝ) : Prop := 0 < eps ∧ eps < 1 / 100

/-- Forward step of the layer construction: (S,A,B) ↦ (S',A',B'). -/
def rudinStep (eps : ℝ) (st : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let S := st.1
  let A := st.2.1
  let B := st.2.2
  let S' := rudinM eps * A
  let A' := (A - 2 * B) / 4
  let B' := if A' / S' < rudinV eps then S' - A' - rudinM eps * A' else S' - A'
  (S', A', B')

/-- Initial state: S₀ = 1, A₀ = 1/(2V), B₀ = 1 − A₀ − M·A₀. -/
def rudinInit (eps : ℝ) : ℝ × ℝ × ℝ :=
  (1, 1 / (2 * rudinV eps),
    1 - 1 / (2 * rudinV eps) - rudinM eps * (1 / (2 * rudinV eps)))

/-- `S_i`: minimum load of the prefix up to layer i when all layers are split. -/
def rudinS (eps : ℝ) (i : ℕ) : ℝ := ((rudinStep eps)^[i] (rudinInit eps)).1

/-- `A_i`: size of the small jobs of layer i. -/
def rudinA (eps : ℝ) (i : ℕ) : ℝ := ((rudinStep eps)^[i] (rudinInit eps)).2.1

/-- `B_i`: size of the jobs of the type-1 layer i. -/
def rudinB (eps : ℝ) (i : ℕ) : ℝ := ((rudinStep eps)^[i] (rudinInit eps)).2.2

/-- `R_i = A_i / S_i`. -/
def rudinR (eps : ℝ) (i : ℕ) : ℝ := rudinA eps i / rudinS eps i

/-! ### Rational bounds on √2 and √3 -/

private lemma sqrt3_gt : (173 / 100 : ℝ) < Real.sqrt 3 := by
  have hle : (173 / 100 : ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt' (by norm_num : 0 < (173 / 100 : ℝ))).2 (by norm_num)
  exact lt_of_le_of_ne hle (by
    intro h
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
    nlinarith [congrArg (fun z : ℝ => z ^ 2) h, hs])

private lemma sqrt3_lt : Real.sqrt 3 < (26 / 15 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : 0 < (26 / 15 : ℝ))]
  norm_num

private lemma sqrt2_lt : Real.sqrt 2 < (71 / 50 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : 0 < (71 / 50 : ℝ))]
  norm_num

/-! ### Basic bounds on V and M -/

/-- V > √2/2 (since ε < 1/100). -/
lemma rudinV_gt_sqrt2_half (eps : ℝ) (heps : eps < 1 / 100) : Real.sqrt 2 / 2 < rudinV eps := by
  have h1 : (71 / 100 : ℝ) < rudinV eps := by
    dsimp [rudinV]
    nlinarith [sqrt3_gt, heps]
  have h2 : Real.sqrt 2 / 2 < (71 / 100 : ℝ) := by
    nlinarith [sqrt2_lt]
  exact lt_trans h2 h1

/-- V > 0. -/
lemma rudinV_pos (eps : ℝ) (h : rudinOK eps) : 0 < rudinV eps := by
  have h1 := rudinV_gt_sqrt2_half eps h.2
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

/-- V > 2/3. -/
lemma rudinV_gt_two_thirds (eps : ℝ) (h : rudinOK eps) : (2 / 3 : ℝ) < rudinV eps := by
  have h1 := rudinV_gt_sqrt2_half eps h.2
  have h2 : (2 / 3 : ℝ) < Real.sqrt 2 / 2 := by
    have hle : (4 / 3 : ℝ) < Real.sqrt 2 := by
      have hle' : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
        (Real.le_sqrt' (by norm_num : 0 < (4 / 3 : ℝ))).2 (by norm_num)
      exact lt_of_le_of_ne hle' (by
        intro h
        have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
        nlinarith [congrArg (fun z : ℝ => z ^ 2) h, hs])
    nlinarith
  exact lt_trans h2 h1

/-- V < √3 − 1. -/
lemma rudinV_lt (eps : ℝ) (h : rudinOK eps) : rudinV eps < Real.sqrt 3 - 1 := by
  dsimp [rudinV]
  linarith [h.1]

/-- V < 11/15. -/
lemma rudinV_lt_eleven_fifteenth (eps : ℝ) (h : rudinOK eps) : rudinV eps < (11 / 15 : ℝ) := by
  have h1 : rudinV eps < Real.sqrt 3 - 1 := rudinV_lt eps h
  have h2 : Real.sqrt 3 - 1 < (11 / 15 : ℝ) := by
    nlinarith [sqrt3_lt]
  exact lt_trans h1 h2

/-- M > 0. -/
lemma rudinM_pos (eps : ℝ) (h : rudinOK eps) : 0 < rudinM eps := by
  dsimp [rudinM]
  nlinarith [rudinV_gt_two_thirds eps h]

/-- M < 1/10. -/
lemma rudinM_lt_one_tenth (eps : ℝ) (h : rudinOK eps) : rudinM eps < 1 / 10 := by
  dsimp [rudinM]
  nlinarith [rudinV_lt_eleven_fifteenth eps h]

/-! ### Initial values and recurrence identities -/

lemma rudinS_zero (eps : ℝ) : rudinS eps 0 = 1 := by
  simp [rudinS, rudinInit]

lemma rudinA_zero (eps : ℝ) : rudinA eps 0 = 1 / (2 * rudinV eps) := by
  simp [rudinA, rudinInit]

lemma rudinB_zero (eps : ℝ) (hV : rudinV eps ≠ 0) : rudinB eps 0 = 1 / 4 := by
  simp [rudinB, rudinInit, rudinM]
  field_simp [hV]
  ring_nf

lemma rudinR_zero (eps : ℝ) : rudinR eps 0 = 1 / (2 * rudinV eps) := by
  simp [rudinR, rudinA_zero, rudinS_zero]

lemma rudinS_succ (eps : ℝ) (i : ℕ) : rudinS eps i.succ = rudinM eps * rudinA eps i := by
  rw [show i.succ = i + 1 by omega]
  rw [rudinS, rudinA, Function.iterate_succ']
  simp only [Function.comp_apply]
  rfl

lemma rudinA_succ (eps : ℝ) (i : ℕ) :
    rudinA eps i.succ = (rudinA eps i - 2 * rudinB eps i) / 4 := by
  rw [show i.succ = i + 1 by omega]
  rw [rudinA, rudinB, Function.iterate_succ']
  simp only [Function.comp_apply]
  rfl

lemma rudinB_succ (eps : ℝ) (i : ℕ) :
    rudinB eps i.succ =
      if rudinR eps i.succ < rudinV eps
        then rudinS eps i.succ - rudinA eps i.succ - rudinM eps * rudinA eps i.succ
        else rudinS eps i.succ - rudinA eps i.succ := by
  rw [show i.succ = i + 1 by omega]
  rw [rudinB, rudinR, rudinS, rudinA, Function.iterate_succ']
  simp only [Function.comp_apply]
  unfold rudinStep
  rfl

lemma rudinB_succ_of_lt (eps : ℝ) (i : ℕ) (h : rudinR eps i.succ < rudinV eps) :
    rudinB eps i.succ = rudinS eps i.succ - rudinA eps i.succ - rudinM eps * rudinA eps i.succ := by
  rw [rudinB_succ, if_pos h]

lemma rudinB_succ_of_ge (eps : ℝ) (i : ℕ) (h : rudinV eps ≤ rudinR eps i.succ) :
    rudinB eps i.succ = rudinS eps i.succ - rudinA eps i.succ := by
  rw [rudinB_succ, if_neg]
  exact fun hlt => not_le_of_gt hlt h

/-- `B_i` takes the "continuing" form whenever R_i < V. -/
lemma rudinB_of_lt (eps : ℝ) (i : ℕ) (h : rudinR eps i < rudinV eps) :
    rudinB eps i = rudinS eps i - rudinA eps i - rudinM eps * rudinA eps i := by
  cases i with
  | zero =>
      have hV : rudinV eps ≠ 0 := by
        intro hz
        have h' : rudinR eps 0 < rudinV eps := h
        rw [hz] at h'
        rw [rudinR_zero] at h'
        simpa [hz] using h'
      calc
        rudinB eps 0 = 1 / 4 := rudinB_zero eps hV
        _ = rudinS eps 0 - rudinA eps 0 - rudinM eps * rudinA eps 0 := by
          rw [rudinS_zero, rudinA_zero]
          dsimp [rudinM]
          field_simp [hV]
          ring_nf
  | succ i =>
      simpa [Nat.succ_eq_add_one] using rudinB_succ_of_lt eps i h

/-! ### Ratio recurrence -/

/-- A_i = 2B_i + 4A_{i+1}. -/
lemma rudinA_eq (eps : ℝ) (i : ℕ) : rudinA eps i = 2 * rudinB eps i + 4 * rudinA eps i.succ := by
  have h := rudinA_succ eps i
  have hB : 4 * rudinA eps i.succ = rudinA eps i - 2 * rudinB eps i := by
    nlinarith [h]
  linarith

/-- While R_i < V (continuing case), R_{i+1} = 3/(4M) + 1/2 − 1/(2·M·R_i). -/
lemma rudinR_succ_of_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (h : rudinR eps i < rudinV eps) (hS : rudinS eps i ≠ 0) (hA : rudinA eps i ≠ 0) :
    rudinR eps i.succ = rudin_R_step (rudinV eps) (rudinR eps i) := by
  have hB := rudinB_of_lt eps i h
  have hS' : rudinS eps i.succ ≠ 0 := by
    rw [rudinS_succ]
    exact mul_ne_zero (ne_of_gt (rudinM_pos eps hOK)) hA
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  dsimp [rudinR, rudin_R_step]
  rw [rudinA_succ, rudinS_succ]
  rw [hB]
  field_simp [hM, hM3, hS, hA, hS', rudinM]
  rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]
  norm_num
  ring_nf

/-! ### Ratio increments (Lemma 3.2) -/

/-- δ_i = R_{i+1} − R_i. -/
def rudinDelta (eps : ℝ) (i : ℕ) : ℝ := rudinR eps i.succ - rudinR eps i

/-- R₀ = 1/(2V) < V. -/
lemma rudinR_zero_lt (eps : ℝ) (hOK : rudinOK eps) : rudinR eps 0 < rudinV eps := by
  have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
  have hVgt := rudinV_gt_sqrt2_half eps hOK.2
  have hsq : (1 / 2 : ℝ) < rudinV eps ^ 2 := by
    have hle : |Real.sqrt 2 / 2| < |rudinV eps| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 / 2),
        abs_of_nonneg (le_of_lt hVpos)]
      exact hVgt
    have hs := sq_lt_sq.mpr hle
    have hsq2 : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    nlinarith
  rw [rudinR_zero]
  rw [div_lt_iff₀ (by positivity : 0 < 2 * rudinV eps)]
  nlinarith [hsq]

/-- δ₁ = (2 − 2V − V²) / (4·M·V). -/
lemma rudinDelta_one (eps : ℝ) (hOK : rudinOK eps) :
    rudinDelta eps 0 =
      (2 - 2 * rudinV eps - rudinV eps ^ 2) / (4 * rudinM eps * rudinV eps) := by
  have hV : rudinV eps ≠ 0 := ne_of_gt (rudinV_pos eps hOK)
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  have hS0 : rudinS eps 0 ≠ 0 := by rw [rudinS_zero]; norm_num
  have hA0 : rudinA eps 0 ≠ 0 := by
    rw [rudinA_zero]
    exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hV)
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  have hR1 : rudinR eps 1 = rudin_R_step (rudinV eps) (rudinR eps 0) :=
    rudinR_succ_of_lt eps hOK 0 (rudinR_zero_lt eps hOK) hS0 hA0
  dsimp [rudinDelta]
  rw [hR1, rudinR_zero]
  dsimp [rudin_R_step]
  field_simp [hV, hM, hM3, rudinM]
  rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]
  norm_num
  ring_nf

/-- δ₁ = (2√3·ε − ε²) / (4·M·V). -/
lemma rudinDelta_one' (eps : ℝ) (hOK : rudinOK eps) :
    rudinDelta eps 0 =
      (2 * Real.sqrt 3 * eps - eps ^ 2) / (4 * rudinM eps * rudinV eps) := by
  have hsq : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  rw [rudinDelta_one eps hOK]
  dsimp [rudinV]
  ring_nf
  rw [hsq]
  ring

/-- δ₁ > 11·ε > 0. -/
lemma rudinDelta_one_pos (eps : ℝ) (hOK : rudinOK eps) : 11 * eps < rudinDelta eps 0 := by
  have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
  have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
  have hd : rudinDelta eps 0 =
      (2 * Real.sqrt 3 * eps - eps ^ 2) / (4 * rudinM eps * rudinV eps) :=
    rudinDelta_one' eps hOK
  rw [hd]
  -- (2√3·ε − ε²)/(4MV) > 11ε  ⟺  2√3 − ε > 44·M·V   (4MV > 0, ε > 0)
  have h44 : 44 * rudinM eps * rudinV eps < 2 * Real.sqrt 3 - eps := by
    have hMlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
    have hVlt : rudinV eps < 11 / 15 := rudinV_lt_eleven_fifteenth eps hOK
    have hsq3 : (173 / 100 : ℝ) < Real.sqrt 3 := sqrt3_gt
    have h44' : 44 * rudinM eps * rudinV eps < 242 / 75 := by
      nlinarith [hMlt, hVlt]
    have hright : 242 / 75 < 2 * Real.sqrt 3 - eps := by
      have hle : (242 / 75 : ℝ) < 2 * (173 / 100) - 1 / 100 := by norm_num
      nlinarith [hsq3, hOK.2]
    exact lt_trans h44' hright
  have hleft : 0 < 4 * rudinM eps * rudinV eps := by positivity
  have hgt : 11 * eps < (2 * Real.sqrt 3 * eps - eps ^ 2) / (4 * rudinM eps * rudinV eps) := by
    have heps : 0 < eps := hOK.1
    rw [lt_div_iff₀ hleft]
    have hmul : 44 * eps * rudinM eps * rudinV eps < eps * (2 * Real.sqrt 3 - eps) := by
      have h := mul_lt_mul_of_pos_left h44 heps
      nlinarith
    nlinarith
  simpa [hd] using hgt

/-- R_i ≠ 0 whenever A_i ≠ 0 and S_i ≠ 0. -/
lemma rudinR_ne_zero (eps : ℝ) (i : ℕ) (hA : rudinA eps i ≠ 0) (hS : rudinS eps i ≠ 0) :
    rudinR eps i ≠ 0 := by
  exact div_ne_zero hA hS

/-- f(R') − f(R) = (R' − R) / (2·M·R'·R) for the ratio step f (M = (3V−2)/2). -/
private lemma rudin_R_step_sub (V R R' : ℝ) (hM : 3 * V - 2 ≠ 0) (hR : R ≠ 0) (hR' : R' ≠ 0) :
    rudin_R_step V R' - rudin_R_step V R =
      (R' - R) / (2 * ((3 * V - 2) / 2) * R' * R) := by
  dsimp [rudin_R_step]
  field_simp [hM, hR, hR']
  ring

/-- A tighter bound on √3, needed for the growth factor 9.5. -/
private lemma sqrt3_lt_362_209 : Real.sqrt 3 < (362 / 209 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : 0 < (362 / 209 : ℝ))]
  norm_num

/-- M·V² < 1/19. -/
lemma rudin_MVV_lt (eps : ℝ) (hOK : rudinOK eps) :
    rudinM eps * rudinV eps ^ 2 < 1 / 19 := by
  have hV : 0 < rudinV eps := rudinV_pos eps hOK
  have hVlt : rudinV eps < Real.sqrt 3 - 1 := rudinV_lt eps hOK
  have hV23 : (2 / 3 : ℝ) < rudinV eps := rudinV_gt_two_thirds eps hOK
  have hsq : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have h13 : (3 * rudinV eps - 2) * rudinV eps ^ 2 < 22 * Real.sqrt 3 - 38 := by
    have h1 : 3 * rudinV eps - 2 < 3 * Real.sqrt 3 - 5 := by nlinarith [hVlt]
    have h2 : rudinV eps ^ 2 < (Real.sqrt 3 - 1) ^ 2 := by
      have hle : rudinV eps ≤ Real.sqrt 3 - 1 := le_of_lt hVlt
      exact sq_lt_sq.mpr (by
        rw [abs_of_pos hV]
        rw [abs_of_pos (by nlinarith [sqrt3_gt])]
        exact hVlt)
    have h3 : 0 < 3 * rudinV eps - 2 := by nlinarith [hV23]
    have h4 : 0 < rudinV eps ^ 2 := by
      rw [pow_two]
      exact mul_pos hV hV
    calc
      (3 * rudinV eps - 2) * rudinV eps ^ 2
          < (3 * Real.sqrt 3 - 5) * rudinV eps ^ 2 :=
        mul_lt_mul_of_pos_right h1 h4
      _ < (3 * Real.sqrt 3 - 5) * (Real.sqrt 3 - 1) ^ 2 := by
        have h5 : 0 < 3 * Real.sqrt 3 - 5 := by nlinarith [sqrt3_gt]
        exact mul_lt_mul_of_pos_left h2 h5
      _ = 22 * Real.sqrt 3 - 38 := by
        have hsq1 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
          rw [sub_sq, hsq]
          ring
        calc
          (3 * Real.sqrt 3 - 5) * (Real.sqrt 3 - 1) ^ 2
              = (3 * Real.sqrt 3 - 5) * (4 - 2 * Real.sqrt 3) := by
                rw [hsq1]
          _ = 22 * Real.sqrt 3 - 38 := by
                ring_nf
                rw [hsq]
                ring
  have h14 : rudinM eps * rudinV eps ^ 2 < 11 * Real.sqrt 3 - 19 := by
    dsimp [rudinM]
    nlinarith [h13]
  have h15 : 11 * Real.sqrt 3 - 19 < 1 / 19 := by
    nlinarith [sqrt3_lt_362_209]
  exact lt_trans h14 h15

/-- While R_i < V and R_{i+1} < V (continuing case), δ_{i+1} = δ_i / (2·M·R_{i+1}·R_i). -/
lemma rudinDelta_succ (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : rudinR eps i < rudinV eps) (hi' : rudinR eps i.succ < rudinV eps)
    (hRi : rudinR eps i ≠ 0) (hR1 : rudinR eps i.succ ≠ 0) :
    rudinDelta eps i.succ =
      rudinDelta eps i / (2 * rudinM eps * rudinR eps i.succ * rudinR eps i) := by
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  have hS : rudinS eps i ≠ 0 := by
    intro hz
    apply hRi
    dsimp [rudinR]
    rw [hz]
    simp
  have hA : rudinA eps i ≠ 0 := by
    intro hz
    apply hRi
    dsimp [rudinR]
    rw [hz]
    simp
  have hS1 : rudinS eps i.succ ≠ 0 := by
    intro hz
    apply hR1
    dsimp [rudinR]
    rw [hz]
    simp
  have hA1 : rudinA eps i.succ ≠ 0 := by
    intro hz
    apply hR1
    dsimp [rudinR]
    rw [hz]
    simp
  have h1 : rudinR eps i.succ = rudin_R_step (rudinV eps) (rudinR eps i) :=
    rudinR_succ_of_lt eps hOK i hi hS hA
  have h2 : rudinR eps i.succ.succ = rudin_R_step (rudinV eps) (rudinR eps i.succ) :=
    rudinR_succ_of_lt eps hOK i.succ hi' hS1 hA1
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  have hsub := rudin_R_step_sub (rudinV eps) (rudinR eps i) (rudinR eps i.succ) hM3 hRi hR1
  have hfR : rudin_R_step (rudinV eps) (rudinR eps i) ≠ 0 := by
    rw [← h1]
    exact hR1
  dsimp [rudinDelta]
  calc
    rudinR eps i.succ.succ - rudinR eps i.succ
        = rudin_R_step (rudinV eps) (rudinR eps i.succ) - rudinR eps i.succ := by
          rw [h2]
    _ = rudin_R_step (rudinV eps) (rudin_R_step (rudinV eps) (rudinR eps i)) -
          rudin_R_step (rudinV eps) (rudinR eps i) := by
          rw [h1]
    _ = (rudin_R_step (rudinV eps) (rudinR eps i) - rudinR eps i) /
          (2 * ((3 * rudinV eps - 2) / 2) *
            rudin_R_step (rudinV eps) (rudinR eps i) * rudinR eps i) := by
          exact rudin_R_step_sub (rudinV eps) (rudinR eps i)
            (rudin_R_step (rudinV eps) (rudinR eps i)) hM3 hRi hfR
    _ = rudinDelta eps i /
          (2 * rudinM eps * rudinR eps i.succ * rudinR eps i) := by
          dsimp [rudinDelta]
          rw [← h1]
          rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]

/-- While continuing, δ_{i+1} > (19/2)·δ_i. -/
lemma rudinDelta_succ_gt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : rudinR eps i < rudinV eps) (hi' : rudinR eps i.succ < rudinV eps)
    (hRi : rudinR eps i ≠ 0) (hR1 : rudinR eps i.succ ≠ 0)
    (hposR : 0 < rudinR eps i) (hposR1 : 0 < rudinR eps i.succ)
    (hpos : 0 < rudinDelta eps i) :
    (19 / 2 : ℝ) * rudinDelta eps i < rudinDelta eps i.succ := by
  have hd := rudinDelta_succ eps hOK i hi hi' hRi hR1
  rw [hd]
  -- δ_{i+1} = δ_i/(2MRR) > (19/2)δ_i  ⟺  M·R_{i+1}·R_i < 1/19
  have hMVV : rudinM eps * rudinV eps ^ 2 < 1 / 19 := rudin_MVV_lt eps hOK
  have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
  have hMRR : rudinM eps * rudinR eps i.succ * rudinR eps i < 1 / 19 := by
    have h1 : rudinR eps i.succ * rudinR eps i < rudinV eps ^ 2 := by
      nlinarith [hposR, hposR1, hi, hi']
    have h2 : rudinM eps * (rudinR eps i.succ * rudinR eps i) < rudinM eps * rudinV eps ^ 2 :=
      mul_lt_mul_of_pos_left h1 hMpos
    nlinarith [h2, hMVV]
  have hden : 0 < 2 * rudinM eps * rudinR eps i.succ * rudinR eps i := by
    positivity
  rw [lt_div_iff₀ hden]
  have hmain : (19 / 2 : ℝ) * (2 * rudinM eps * rudinR eps i.succ * rudinR eps i) < 1 := by
    nlinarith [hMRR]
  have hmul : (19 / 2 : ℝ) * (2 * rudinM eps * rudinR eps i.succ * rudinR eps i) *
      rudinDelta eps i < rudinDelta eps i := by
    have h := mul_lt_mul_of_pos_left hmain hpos
    nlinarith
  nlinarith [hmul]

/-! ### Termination (Lemma 3.2) -/

/-- The recurrence terminates: some R_i reaches V. -/
lemma rudin_terminates (eps : ℝ) (hOK : rudinOK eps) : ∃ n : ℕ, rudinV eps ≤ rudinR eps n := by
  by_contra h_never
  push_neg at h_never
  have hV : 0 < rudinV eps := rudinV_pos eps hOK
  have hM : 0 < rudinM eps := rudinM_pos eps hOK
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply ne_of_gt hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  have hR0pos : 0 < rudinR eps 0 := by
    rw [rudinR_zero]
    exact div_pos (by norm_num) (mul_pos (by norm_num) hV)
  -- 1. positivity and R₀ ≤ R_i along the continuing path
  have hpos : ∀ i, 0 < rudinS eps i ∧ 0 < rudinA eps i ∧ 0 < rudinR eps i ∧
      rudinR eps 0 ≤ rudinR eps i := by
    intro i
    induction i with
    | zero =>
        constructor
        · rw [rudinS_zero]; norm_num
        · constructor
          · rw [rudinA_zero]
            exact div_pos (by norm_num) (mul_pos (by norm_num) hV)
          · constructor
            · exact hR0pos
            · rfl
    | succ i ih =>
        rcases ih with ⟨hS, hA, hR, hR0⟩
        have hS' : 0 < rudinS eps i.succ := by
          rw [rudinS_succ]
          exact mul_pos hM hA
        have hf : rudinR eps i.succ = rudin_R_step (rudinV eps) (rudinR eps i) :=
          rudinR_succ_of_lt eps hOK i (h_never i) (ne_of_gt hS) (ne_of_gt hA)
        have hR1eq : rudin_R_step (rudinV eps) (rudinR eps 0) = rudinR eps 1 := by
          have h1 : rudinR eps 1 = rudin_R_step (rudinV eps) (rudinR eps 0) :=
            rudinR_succ_of_lt eps hOK 0 (rudinR_zero_lt eps hOK)
              (by rw [rudinS_zero]; norm_num)
              (by rw [rudinA_zero]; exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (ne_of_gt hV)))
          exact h1.symm
        have hd0 : 0 < rudinDelta eps 0 :=
          lt_trans (by linarith [hOK.1]) (rudinDelta_one_pos eps hOK)
        have hR1gt0 : 0 < rudinR eps 1 := by
          have hR1' : rudinR eps 1 = rudinR eps 0 + rudinDelta eps 0 := by
            dsimp [rudinDelta]
            linarith
          rw [hR1']
          nlinarith [hR0pos, hd0]
        have hmono : rudin_R_step (rudinV eps) (rudinR eps 0) ≤
            rudin_R_step (rudinV eps) (rudinR eps i) := by
          have hsub := rudin_R_step_sub (rudinV eps) (rudinR eps 0) (rudinR eps i)
            hM3 (ne_of_gt hR0pos) (ne_of_gt hR)
          rw [← sub_nonneg]
          rw [hsub]
          have hM3pos : 0 < 3 * rudinV eps - 2 := by nlinarith [rudinV_gt_two_thirds eps hOK]
          have hM'pos : 0 < (3 * rudinV eps - 2) / 2 := div_pos hM3pos (by norm_num)
          have hden : 0 < 2 * ((3 * rudinV eps - 2) / 2) * rudinR eps i * rudinR eps 0 :=
            mul_pos (mul_pos (mul_pos (by norm_num) hM'pos) hR) hR0pos
          exact div_nonneg (by linarith) (le_of_lt hden)
        have hR' : 0 < rudinR eps i.succ := by
          rw [hf]
          have hpos1 : 0 < rudin_R_step (rudinV eps) (rudinR eps 0) := by
            rw [hR1eq]
            exact hR1gt0
          linarith [hmono, hpos1]
        have hA' : 0 < rudinA eps i.succ := by
          have hB := rudinB_of_lt eps i (h_never i)
          have hAeq : rudinA eps i.succ = (rudinA eps i * (1 + 3 * rudinV eps) - 2 * rudinS eps i) / 4 := by
            rw [rudinA_succ, hB]
            dsimp [rudinM]
            ring
          rw [hAeq]
          have hVlt1 : rudinV eps < 1 := by
            have h1 := rudinV_lt eps hOK
            nlinarith [sqrt3_lt]
          have hR0gt : 2 / (1 + 3 * rudinV eps) < 1 / (2 * rudinV eps) := by
            have hpos1 : 0 < 2 * rudinV eps := mul_pos (by norm_num) hV
            have hpos2 : 0 < 1 + 3 * rudinV eps := by nlinarith [hV]
            have hmain : 2 * (2 * rudinV eps) < 1 * (1 + 3 * rudinV eps) := by
              nlinarith [hVlt1]
            exact (div_lt_div_iff₀ hpos2 hpos1).2 hmain
          have hR0le' : 1 / (2 * rudinV eps) ≤ rudinR eps i := by
            rw [rudinR_zero] at hR0
            exact hR0
          have hgt : 2 / (1 + 3 * rudinV eps) < rudinR eps i :=
            lt_of_lt_of_le hR0gt hR0le'
          have h1 : (2 / (1 + 3 * rudinV eps)) * rudinS eps i < rudinR eps i * rudinS eps i :=
            mul_lt_mul_of_pos_right hgt hS
          have hAeq' : rudinR eps i * rudinS eps i = rudinA eps i := by
            dsimp [rudinR]
            field_simp [ne_of_gt hS]
          rw [hAeq'] at h1
          have hpos13 : 0 < 1 + 3 * rudinV eps := by nlinarith [hV]
          have h2 : 2 * rudinS eps i < rudinA eps i * (1 + 3 * rudinV eps) := by
            have hmul := mul_lt_mul_of_pos_right h1 hpos13
            have hleft : (2 / (1 + 3 * rudinV eps)) * rudinS eps i * (1 + 3 * rudinV eps) =
                2 * rudinS eps i := by
              field_simp [ne_of_gt hpos13]
            rw [hleft] at hmul
            exact hmul
          nlinarith
        constructor
        · exact hS'
        · constructor
          · exact hA'
          · constructor
            · exact hR'
            · rw [hf]
              have h1 : rudinR eps 0 ≤ rudin_R_step (rudinV eps) (rudinR eps 0) := by
                rw [hR1eq]
                have hR1' : rudinR eps 1 = rudinR eps 0 + rudinDelta eps 0 := by
                  dsimp [rudinDelta]
                  linarith
                rw [hR1']
                nlinarith [hd0]
              linarith [hmono, h1]
  -- 2. all increments are positive
  have hdpos : ∀ i, 0 < rudinDelta eps i := by
    intro i
    induction i with
    | zero => exact lt_trans (by linarith [hOK.1]) (rudinDelta_one_pos eps hOK)
    | succ i ih =>
        rcases hpos i with ⟨hS, hA, hR, hR0⟩
        rcases hpos i.succ with ⟨hS1, hA1, hR1, hR0'⟩
        have hgt := rudinDelta_succ_gt eps hOK i (h_never i) (h_never i.succ)
          (ne_of_gt hR) (ne_of_gt hR1) hR hR1 ih
        linarith
  -- 3. exponential growth of increments
  have hdlt : ∀ i, rudinDelta eps 0 * (19 / 2 : ℝ) ^ i ≤ rudinDelta eps i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rcases hpos i with ⟨hS, hA, hR, hR0⟩
        rcases hpos i.succ with ⟨hS1, hA1, hR1, hR0'⟩
        have hgt' := rudinDelta_succ_gt eps hOK i (h_never i) (h_never i.succ)
          (ne_of_gt hR) (ne_of_gt hR1) hR hR1 (hdpos i)
        calc
          rudinDelta eps 0 * (19 / 2 : ℝ) ^ i.succ
              = rudinDelta eps 0 * (19 / 2 : ℝ) ^ i * (19 / 2) := by
                rw [pow_succ]
                ring
          _ ≤ rudinDelta eps i * (19 / 2) := by
                exact mul_le_mul_of_nonneg_right ih (by norm_num : 0 ≤ (19 / 2 : ℝ))
          _ ≤ rudinDelta eps i.succ := by
                have h := le_of_lt hgt'
                nlinarith
  -- 4. lower bound on R_i (geometric series)
  have hRge : ∀ i, rudinR eps 0 + rudinDelta eps 0 *
      (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1)) ≤ rudinR eps i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        have hsum : (((19 / 2 : ℝ) ^ i.succ - 1) / (19 / 2 - 1)) =
            (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1)) + (19 / 2 : ℝ) ^ i := by
          rw [pow_succ]
          field_simp [show (19 / 2 : ℝ) - 1 ≠ 0 by norm_num]
          ring
        calc
          rudinR eps 0 + rudinDelta eps 0 * (((19 / 2 : ℝ) ^ i.succ - 1) / (19 / 2 - 1))
              = (rudinR eps 0 + rudinDelta eps 0 * (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1))) +
                  rudinDelta eps 0 * (19 / 2 : ℝ) ^ i := by
                rw [hsum]
                ring
          _ ≤ rudinR eps i + rudinDelta eps 0 * (19 / 2 : ℝ) ^ i := by linarith [ih]
          _ ≤ rudinR eps i + rudinDelta eps i := by
                have hd : rudinDelta eps 0 * (19 / 2 : ℝ) ^ i ≤ rudinDelta eps i := hdlt i
                linarith
          _ = rudinR eps i.succ := by
                have hRsucc : rudinR eps i.succ = rudinR eps i + rudinDelta eps i := by
                  dsimp [rudinDelta]
                  linarith
                rw [hRsucc]
  -- 5. R_i is unbounded, contradicting R_i < V for all i
  have hpow : ∀ C : ℝ, ∃ i : ℕ, C ≤ (19 / 2 : ℝ) ^ i := by
    intro C
    have hge : ∀ i : ℕ, (i : ℝ) ≤ (2 : ℝ) ^ i := by
      intro i
      induction i with
      | zero => norm_num
      | succ i ih =>
          have h1 : (i : ℝ) ≤ (2 : ℝ) ^ i := ih
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ i := by
            have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2) i
            simpa using h
          have h3 : (2 : ℝ) ^ i * 2 = (2 : ℝ) ^ i + (2 : ℝ) ^ i := by ring
          have h4 : (i : ℝ) + 1 ≤ (2 : ℝ) ^ i + (2 : ℝ) ^ i := by nlinarith
          simpa [pow_succ, h3] using h4
    rcases exists_nat_ge C with ⟨i, hi⟩
    refine ⟨i.succ, ?_⟩
    have h19 : (2 : ℝ) ^ i.succ ≤ (19 / 2 : ℝ) ^ i.succ :=
      pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : (2 : ℝ) ≤ 19 / 2) _
    calc
      C ≤ (i : ℝ) := hi
      _ ≤ (2 : ℝ) ^ i := hge i
      _ ≤ (2 : ℝ) ^ i.succ := by
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : 0 < (2 : ℝ)) i]
      _ ≤ (19 / 2 : ℝ) ^ i.succ := h19
  have hC : ∃ i, rudinV eps ≤ rudinR eps i := by
    let C := (rudinV eps - rudinR eps 0) * (19 / 2 - 1) / rudinDelta eps 0 + 1
    rcases hpow C with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hd0 : 0 < rudinDelta eps 0 := hdpos 0
    have hg : 0 < (19 / 2 : ℝ) - 1 := by norm_num
    have hR0' : 0 ≤ rudinR eps 0 := by
      rw [rudinR_zero]
      exact le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) hV))
    have hCge : (rudinV eps - rudinR eps 0) * (19 / 2 - 1) ≤
        rudinDelta eps 0 * ((19 / 2 : ℝ) ^ i - 1) := by
      have hmul : ((rudinV eps - rudinR eps 0) * (19 / 2 - 1) / rudinDelta eps 0) ≤
          (19 / 2 : ℝ) ^ i - 1 := by
        dsimp [C] at hi
        linarith
      have h1 := (div_le_iff₀ hd0).mp hmul
      nlinarith [h1]
    have hVle : rudinV eps ≤ rudinR eps 0 + rudinDelta eps 0 *
        (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1)) := by
      have h1 : rudinV eps - rudinR eps 0 ≤ rudinDelta eps 0 *
          (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1)) := by
        have h2 := (le_div_iff₀ hg).mpr hCge
        calc
          rudinV eps - rudinR eps 0
              ≤ (rudinDelta eps 0 * ((19 / 2 : ℝ) ^ i - 1)) / (19 / 2 - 1) := h2
          _ = rudinDelta eps 0 * (((19 / 2 : ℝ) ^ i - 1) / (19 / 2 - 1)) := by
                field_simp [ne_of_gt hg]
      linarith
    exact le_trans hVle (hRge i)
  rcases hC with ⟨i, hi⟩
  exact False.elim (not_lt_of_ge hi (h_never i))

/-! ### The terminal index n -/

/-- The first index at which R reaches V. -/
noncomputable def rudinN (eps : ℝ) (hOK : rudinOK eps) : ℕ :=
  Nat.find (rudin_terminates eps hOK)

lemma rudinN_spec (eps : ℝ) (hOK : rudinOK eps) :
    rudinV eps ≤ rudinR eps (rudinN eps hOK) :=
  Nat.find_spec (rudin_terminates eps hOK)

lemma rudinN_min (eps : ℝ) (hOK : rudinOK eps) (k : ℕ) (hk : rudinV eps ≤ rudinR eps k) :
    rudinN eps hOK ≤ k :=
  Nat.find_min' (rudin_terminates eps hOK) hk

/-- Before the terminal index the construction is still in the continuing case. -/
lemma rudinN_ratio_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    rudinR eps i < rudinV eps := by
  by_contra h
  have hge : rudinV eps ≤ rudinR eps i := le_of_not_gt h
  have hn : rudinN eps hOK ≤ i := rudinN_min eps hOK i hge
  linarith

lemma rudinN_pos (eps : ℝ) (hOK : rudinOK eps) : 0 < rudinN eps hOK := by
  have hR0lt : rudinR eps 0 < rudinV eps := rudinR_zero_lt eps hOK
  by_contra h
  have hn0 : rudinN eps hOK = 0 := by omega
  have hspec : rudinV eps ≤ rudinR eps (rudinN eps hOK) := rudinN_spec eps hOK
  rw [hn0] at hspec
  linarith

/-- Positivity and R₀ ≤ R_i on the continuing prefix i ≤ n. -/
lemma rudin_pos_le_n (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i ≤ rudinN eps hOK) :
    0 < rudinS eps i ∧ 0 < rudinA eps i ∧ 0 < rudinR eps i ∧ rudinR eps 0 ≤ rudinR eps i := by
  have hV : 0 < rudinV eps := rudinV_pos eps hOK
  have hM : 0 < rudinM eps := rudinM_pos eps hOK
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply ne_of_gt hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  have hR0pos : 0 < rudinR eps 0 := by
    rw [rudinR_zero]
    exact div_pos (by norm_num) (mul_pos (by norm_num) hV)
  induction i with
  | zero =>
      constructor
      · rw [rudinS_zero]; norm_num
      · constructor
        · rw [rudinA_zero]
          exact div_pos (by norm_num) (mul_pos (by norm_num) hV)
        · constructor
          · exact hR0pos
          · rfl
  | succ i ih =>
      have hi_lt : i < rudinN eps hOK := by omega
      rcases ih (le_of_lt hi_lt) with ⟨hS, hA, hR, hR0⟩
      have hS' : 0 < rudinS eps i.succ := by
        rw [rudinS_succ]
        exact mul_pos hM hA
      have hf : rudinR eps i.succ = rudin_R_step (rudinV eps) (rudinR eps i) :=
        rudinR_succ_of_lt eps hOK i (rudinN_ratio_lt eps hOK i hi_lt) (ne_of_gt hS) (ne_of_gt hA)
      have hR1eq : rudin_R_step (rudinV eps) (rudinR eps 0) = rudinR eps 1 := by
        have h1 : rudinR eps 1 = rudin_R_step (rudinV eps) (rudinR eps 0) :=
          rudinR_succ_of_lt eps hOK 0 (rudinR_zero_lt eps hOK)
            (by rw [rudinS_zero]; norm_num)
            (by rw [rudinA_zero]; exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (ne_of_gt hV)))
        exact h1.symm
      have hd0 : 0 < rudinDelta eps 0 :=
        lt_trans (by linarith [hOK.1]) (rudinDelta_one_pos eps hOK)
      have hR1gt0 : 0 < rudinR eps 1 := by
        have hR1' : rudinR eps 1 = rudinR eps 0 + rudinDelta eps 0 := by
          dsimp [rudinDelta]
          linarith
        rw [hR1']
        nlinarith [hR0pos, hd0]
      have hmono : rudin_R_step (rudinV eps) (rudinR eps 0) ≤
          rudin_R_step (rudinV eps) (rudinR eps i) := by
        have hsub := rudin_R_step_sub (rudinV eps) (rudinR eps 0) (rudinR eps i)
          hM3 (ne_of_gt hR0pos) (ne_of_gt hR)
        rw [← sub_nonneg]
        rw [hsub]
        have hM3pos : 0 < 3 * rudinV eps - 2 := by nlinarith [rudinV_gt_two_thirds eps hOK]
        have hM'pos : 0 < (3 * rudinV eps - 2) / 2 := div_pos hM3pos (by norm_num)
        have hden : 0 < 2 * ((3 * rudinV eps - 2) / 2) * rudinR eps i * rudinR eps 0 :=
          mul_pos (mul_pos (mul_pos (by norm_num) hM'pos) hR) hR0pos
        exact div_nonneg (by linarith) (le_of_lt hden)
      have hR' : 0 < rudinR eps i.succ := by
        rw [hf]
        have hpos1 : 0 < rudin_R_step (rudinV eps) (rudinR eps 0) := by
          rw [hR1eq]
          exact hR1gt0
        linarith [hmono, hpos1]
      have hA' : 0 < rudinA eps i.succ := by
        have hB := rudinB_of_lt eps i (rudinN_ratio_lt eps hOK i hi_lt)
        have hAeq : rudinA eps i.succ = (rudinA eps i * (1 + 3 * rudinV eps) - 2 * rudinS eps i) / 4 := by
          rw [rudinA_succ, hB]
          dsimp [rudinM]
          ring
        rw [hAeq]
        have hVlt1 : rudinV eps < 1 := by
          have h1 := rudinV_lt eps hOK
          nlinarith [sqrt3_lt]
        have hR0gt : 2 / (1 + 3 * rudinV eps) < 1 / (2 * rudinV eps) := by
          have hpos1 : 0 < 2 * rudinV eps := mul_pos (by norm_num) hV
          have hpos2 : 0 < 1 + 3 * rudinV eps := by nlinarith [hV]
          have hmain : 2 * (2 * rudinV eps) < 1 * (1 + 3 * rudinV eps) := by
            nlinarith [hVlt1]
          exact (div_lt_div_iff₀ hpos2 hpos1).2 hmain
        have hR0le' : 1 / (2 * rudinV eps) ≤ rudinR eps i := by
          rw [rudinR_zero] at hR0
          exact hR0
        have hgt : 2 / (1 + 3 * rudinV eps) < rudinR eps i :=
          lt_of_lt_of_le hR0gt hR0le'
        have h1 : (2 / (1 + 3 * rudinV eps)) * rudinS eps i < rudinR eps i * rudinS eps i :=
          mul_lt_mul_of_pos_right hgt hS
        have hAeq' : rudinR eps i * rudinS eps i = rudinA eps i := by
          dsimp [rudinR]
          field_simp [ne_of_gt hS]
        rw [hAeq'] at h1
        have hpos13 : 0 < 1 + 3 * rudinV eps := by nlinarith [hV]
        have h2 : 2 * rudinS eps i < rudinA eps i * (1 + 3 * rudinV eps) := by
          have hmul := mul_lt_mul_of_pos_right h1 hpos13
          have hleft : (2 / (1 + 3 * rudinV eps)) * rudinS eps i * (1 + 3 * rudinV eps) =
              2 * rudinS eps i := by
            field_simp [ne_of_gt hpos13]
          rw [hleft] at hmul
          exact hmul
        nlinarith
      constructor
      · exact hS'
      · constructor
        · exact hA'
        · constructor
          · exact hR'
          · rw [hf]
            have h1 : rudinR eps 0 ≤ rudin_R_step (rudinV eps) (rudinR eps 0) := by
              rw [hR1eq]
              have hR1' : rudinR eps 1 = rudinR eps 0 + rudinDelta eps 0 := by
                dsimp [rudinDelta]
                linarith
              rw [hR1']
              nlinarith [hd0]
            linarith [hmono, h1]

/-- At the terminal index (and only there) B takes the terminating form, and
    B_i ≤ A_i/2 holds since R_i ≥ V ≥ 2/3. -/
lemma rudinB_le_half_A (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i ≤ rudinN eps hOK)
    (hge : rudinV eps ≤ rudinR eps i) :
    rudinB eps i ≤ 1 / 2 * rudinA eps i := by
  have hpos := rudin_pos_le_n eps hOK i hi
  rcases hpos with ⟨hS, hA, hR, hR0⟩
  have hB : rudinB eps i = rudinS eps i - rudinA eps i := by
    by_cases hi0 : i = 0
    · subst i
      exfalso
      have hR0lt : rudinR eps 0 < rudinV eps := rudinR_zero_lt eps hOK
      linarith
    · rcases i with _ | i
      · contradiction
      · exact rudinB_succ_of_ge eps i hge
  have hV23 : (2 / 3 : ℝ) ≤ rudinV eps := le_of_lt (rudinV_gt_two_thirds eps hOK)
  have hR23 : (2 / 3 : ℝ) ≤ rudinR eps i := le_trans hV23 hge
  have hAeq : rudinA eps i = rudinR eps i * rudinS eps i := by
    dsimp [rudinR]
    field_simp [ne_of_gt hS]
  have hmain : 1 - rudinR eps i ≤ rudinR eps i / 2 := by
    rw [le_div_iff₀ (by norm_num : 0 < (2 : ℝ))]
    nlinarith [hR23]
  have hfinal : rudinS eps i * (1 - rudinR eps i) ≤ rudinS eps i * (rudinR eps i / 2) :=
    mul_le_mul_of_nonneg_left hmain (le_of_lt hS)
  rw [hB, hAeq]
  nlinarith [hfinal]

/-! ### Packing lemma (Lemma 3.3) -/

/-- The four jobs of layer i: a B-row (four B_i) and an A-row
    (three A_i plus one A_i + 2A_{i+1}; the last layer's A-row is four A_n). -/
def rudinLayerJobs (eps : ℝ) (n : ℕ) (i : ℕ) : List ℝ :=
  [rudinB eps i, rudinB eps i, rudinB eps i, rudinB eps i] ++
  [rudinA eps i, rudinA eps i, rudinA eps i,
    if i = n then rudinA eps i else rudinA eps i + 2 * rudinA eps i.succ]

/-- The jobs of layers n, n−1, ..., i, in that order. -/
def rudinPrefixJobs (eps : ℝ) (n : ℕ) (i : ℕ) : List ℝ :=
  if i ≤ n then rudinLayerJobs eps n i ++ rudinPrefixJobs eps n (i + 1) else []
termination_by n + 1 - i
decreasing_by
  omega

lemma rudinPrefixJobs_eq (eps : ℝ) (n : ℕ) (i : ℕ) (hi : i ≤ n) :
    rudinPrefixJobs eps n i = rudinLayerJobs eps n i ++ rudinPrefixJobs eps n (i + 1) := by
  conv =>
    lhs
    unfold rudinPrefixJobs
  rw [if_pos hi]

lemma rudinPrefixJobs_succ (eps : ℝ) (n : ℕ) (i : ℕ) (hi : i < n) :
    rudinPrefixJobs eps n i = rudinLayerJobs eps n i ++ rudinPrefixJobs eps n (i + 1) :=
  rudinPrefixJobs_eq eps n i (le_of_lt hi)

/-- Lemma 3.3: the jobs of layers n..i can be split into 4 parts of load
    ≤ (3/2)A_i and into 3 parts of load ≤ 2A_i, where n = rudinN. -/
lemma rudin_packing (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i ≤ rudinN eps hOK) :
    (∃ loads : Loads 4, (∀ j : Fin 4, loads j ≤ 3 / 2 * rudinA eps i) ∧
      totalLoad (rudinPrefixJobs eps (rudinN eps hOK) i) = ∑ j : Fin 4, loads j) ∧
    (∃ loads : Loads 3, (∀ j : Fin 3, loads j ≤ 2 * rudinA eps i) ∧
      totalLoad (rudinPrefixJobs eps (rudinN eps hOK) i) = ∑ j : Fin 3, loads j) := by
  let n := rudinN eps hOK
  let P (i : ℕ) : Prop :=
    (∃ loads : Loads 4, (∀ j : Fin 4, loads j ≤ 3 / 2 * rudinA eps i) ∧
      totalLoad (rudinPrefixJobs eps n i) = ∑ j : Fin 4, loads j) ∧
    (∃ loads : Loads 3, (∀ j : Fin 3, loads j ≤ 2 * rudinA eps i) ∧
      totalLoad (rudinPrefixJobs eps n i) = ∑ j : Fin 3, loads j)
  have hbase : P n := by
    dsimp [P]
    constructor
    · refine ⟨fun _ : Fin 4 => rudinB eps n + rudinA eps n, ?_⟩
      constructor
      · intro j
        have hb := rudinB_le_half_A eps hOK n (le_rfl) (rudinN_spec eps hOK)
        nlinarith
      · have hpref : rudinPrefixJobs eps n n = rudinLayerJobs eps n n := by
          unfold rudinPrefixJobs
          rw [if_pos le_rfl]
          unfold rudinPrefixJobs
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
        rw [hpref]
        simp [rudinLayerJobs, totalLoad, Fin.sum_univ_four]
        ring
    · refine ⟨fun j : Fin 3 => if j = 0 then 2 * rudinA eps n
        else rudinA eps n + 2 * rudinB eps n, ?_⟩
      constructor
      · intro j
        have hb := rudinB_le_half_A eps hOK n (le_rfl) (rudinN_spec eps hOK)
        fin_cases j <;> simp <;> nlinarith
      · have hpref : rudinPrefixJobs eps n n = rudinLayerJobs eps n n := by
          unfold rudinPrefixJobs
          rw [if_pos le_rfl]
          unfold rudinPrefixJobs
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
        rw [hpref]
        simp [rudinLayerJobs, totalLoad, Fin.sum_univ_three]
        ring
  have hstep : ∀ k, k + 1 ≤ n → P (n - k) → P (n - (k + 1)) := by
    intro k hk hPk
    let li := n - k
    let li' := n - (k + 1)
    have hli : li = li' + 1 := by dsimp [li, li']; omega
    have hli'le : li' ≤ n := by dsimp [li']; omega
    have hli'lt : li' < n := by dsimp [li']; omega
    have hpref : rudinPrefixJobs eps n li' =
        rudinLayerJobs eps n li' ++ rudinPrefixJobs eps n li := by
      rw [rudinPrefixJobs_eq eps n li' hli'le]
      rw [← hli]
    rcases hPk with ⟨hP4, hP3⟩
    rcases hP4 with ⟨loads4, h4le, h4sum⟩
    rcases hP3 with ⟨loads3, h3le, h3sum⟩
    -- new 3-part packing
    let new3 : Loads 3 := fun j =>
      if j = 0 then 2 * rudinA eps li'
      else if j = 1 then rudinA eps li' + 2 * rudinB eps li' + loads3 0 + loads3 1
      else rudinA eps li' + 2 * rudinA eps li + 2 * rudinB eps li' + loads3 2
    have hAeq : rudinA eps li' = 2 * rudinB eps li' + 4 * rudinA eps li := by
      have h := rudinA_eq eps li'
      have hsucc : li'.succ = li := by omega
      rw [hsucc] at h
      exact h
    have hnew3le : ∀ j : Fin 3, new3 j ≤ 2 * rudinA eps li' := by
      intro j
      fin_cases j <;> simp [new3] <;> nlinarith [h3le 0, h3le 1, h3le 2, hAeq]
    have hnew3sum : totalLoad (rudinPrefixJobs eps n li') = ∑ j : Fin 3, new3 j := by
      rw [hpref]
      dsimp [li]
      rw [show totalLoad (rudinLayerJobs eps n li' ++ rudinPrefixJobs eps n (n - k)) =
          totalLoad (rudinLayerJobs eps n li') + totalLoad (rudinPrefixJobs eps n (n - k)) by
            simp [totalLoad]]
      rw [h3sum]
      simp [Fin.sum_univ_three]
      dsimp [new3]
      simp [rudinLayerJobs, ne_of_lt hli'lt]
      have hsucc1 : li' + 1 = li := by omega
      rw [hsucc1]
      simp [totalLoad]
      norm_num
      ring
    -- new 4-part packing
    let new4 : Loads 4 := fun j =>
      if h : j.val < 3 then rudinA eps li' + rudinB eps li' + loads3 ⟨j.val, h⟩
      else rudinA eps li' + 2 * rudinA eps li + rudinB eps li'
    have hnew4le : ∀ j : Fin 4, new4 j ≤ 3 / 2 * rudinA eps li' := by
      intro j
      by_cases hj : j.val < 3
      · have hle3 : loads3 ⟨j.val, hj⟩ ≤ 2 * rudinA eps li := h3le ⟨j.val, hj⟩
        have hB : rudinB eps li' + 2 * rudinA eps li = 1 / 2 * rudinA eps li' := by
          nlinarith [hAeq]
        simp [new4, hj]
        nlinarith [hle3, hB]
      · simp [new4, hj]
        have hB : rudinB eps li' + 2 * rudinA eps li = 1 / 2 * rudinA eps li' := by
          nlinarith [hAeq]
        nlinarith
    have hnew4sum : totalLoad (rudinPrefixJobs eps n li') = ∑ j : Fin 4, new4 j := by
      rw [hpref]
      dsimp [li]
      rw [show totalLoad (rudinLayerJobs eps n li' ++ rudinPrefixJobs eps n (n - k)) =
          totalLoad (rudinLayerJobs eps n li') + totalLoad (rudinPrefixJobs eps n (n - k)) by
            simp [totalLoad]]
      rw [h3sum]
      simp [Fin.sum_univ_four, Fin.sum_univ_three]
      dsimp [new4]
      simp [rudinLayerJobs, ne_of_lt hli'lt]
      have hsucc1 : li' + 1 = li := by omega
      rw [hsucc1]
      simp [totalLoad]
      norm_num
      ring
    constructor
    · exact ⟨new4, hnew4le, hnew4sum⟩
    · exact ⟨new3, hnew3le, hnew3sum⟩
  have hQ : ∀ k, k ≤ n → P (n - k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa [n] using hbase
    | succ k ih =>
        intro hk
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        exact hstep k (by omega) (ih hk')
  have hP : P i := by
    have h := hQ (n - i) (Nat.sub_le n i)
    have h' : n - (n - i) = i := by omega
    simpa [h'] using h
  simpa [n] using hP

/-! ### Layer separation (Lemma 3.4): numeric bounds -/

/-- For the B-layer violation: 2(M+1−4MR)/(1−MR) > 1+V
    whenever 0 < R < V (with M < 1/10, V < 11/15). -/
lemma rudin_B_ratio_gt (eps : ℝ) (hOK : rudinOK eps) (R : ℝ)
    (hRpos : 0 < R) (hRlt : R < rudinV eps) :
    1 + rudinV eps < 2 * (rudinM eps + 1 - 4 * rudinM eps * R) / (1 - rudinM eps * R) := by
  have hMlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
  have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
  have hVlt : rudinV eps < 11 / 15 := rudinV_lt_eleven_fifteenth eps hOK
  have hRlt15 : R < 11 / 15 := lt_trans hRlt hVlt
  have hdenpos : 0 < 1 - rudinM eps * R := by
    nlinarith [hMlt, hRlt15]
  have heq : 2 * (rudinM eps + 1 - 4 * rudinM eps * R) / (1 - rudinM eps * R) =
      2 - rudinM eps * (6 * R - 2) / (1 - rudinM eps * R) := by
    field_simp [ne_of_gt hdenpos]
    ring
  rw [heq]
  by_cases hRgt : (1 / 3 : ℝ) < R
  · have hnum : rudinM eps * (6 * R - 2) < 6 / 25 := by
      have h61 : 6 * R - 2 < 12 / 5 := by nlinarith [hRlt15]
      have h62 : 0 < 6 * R - 2 := by nlinarith [hRgt]
      nlinarith [hMlt, h61, h62]
    have hden : 139 / 150 < 1 - rudinM eps * R := by
      nlinarith [hMlt, hRlt15]
    have hfrac : rudinM eps * (6 * R - 2) / (1 - rudinM eps * R) < 36 / 139 := by
      rw [div_lt_iff₀ hdenpos]
      nlinarith [hnum, hden]
    have h1 : 1 + rudinV eps < 26 / 15 := by nlinarith [hVlt]
    have h3 : (26 / 15 : ℝ) < 242 / 139 := by norm_num
    have h4 : (242 / 139 : ℝ) = 2 - 36 / 139 := by norm_num
    have h5 : 2 - 36 / 139 < 2 - rudinM eps * (6 * R - 2) / (1 - rudinM eps * R) := by
      nlinarith [hfrac]
    nlinarith [h1, h3, h4, h5]
  · have h6 : 6 * R - 2 ≤ 0 := by nlinarith
    have hnum0 : rudinM eps * (6 * R - 2) ≤ 0 := by nlinarith [hMpos, h6]
    have hfrac0 : rudinM eps * (6 * R - 2) / (1 - rudinM eps * R) ≤ 0 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hnum0]
    have h2 : 1 + rudinV eps < 2 := by
      nlinarith [hVlt]
    nlinarith [hfrac0, h2]

/-- A(M+5/2) = (1+V)·(3/2·A): the A-layer fourth-job violation is tight. -/
lemma rudin_A4_eq (eps : ℝ) (hOK : rudinOK eps) (A : ℝ) :
    A * (rudinM eps + 5 / 2) = (1 + rudinV eps) * (3 / 2 * A) := by
  dsimp [rudinM]
  ring

/-- (N−x)/(D−x) ≥ N/D when D ≤ N, 0 ≤ x and 0 < D−x. -/
lemma div_sub_ge (N D x : ℝ) (hND : D ≤ N) (hx : 0 ≤ x) (hDx : 0 < D - x) :
    N / D ≤ (N - x) / (D - x) := by
  have hD : 0 < D := by nlinarith [hDx, hx]
  rw [div_le_div_iff₀ hD hDx]
  nlinarith [hx, hND]

/-- A second/third A-job violation: the load-to-OPT ratio is still ≥ 1+V. -/
lemma rudin_A23_ratio_ge (eps : ℝ) (hOK : rudinOK eps) (A A' : ℝ)
    (hApos : 0 < A) (hA' : 0 ≤ A') (hDx : 0 < 3 / 2 * A - 2 * A') :
    1 + rudinV eps ≤
      (A * (rudinM eps + 5 / 2) - 2 * A') / (3 / 2 * A - 2 * A') := by
  have heq := rudin_A4_eq eps hOK A
  have hND : 3 / 2 * A ≤ A * (rudinM eps + 5 / 2) := by
    have h1 : 1 ≤ 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
    nlinarith [heq, h1, hApos]
  have hdiv := div_sub_ge (A * (rudinM eps + 5 / 2)) (3 / 2 * A) (2 * A') hND (by nlinarith) hDx
  have hN : A * (rudinM eps + 5 / 2) / (3 / 2 * A) = 1 + rudinV eps := by
    rw [heq]
    have hAp : 0 < 3 / 2 * A := mul_pos (by norm_num) hApos
    field_simp [ne_of_gt hAp]
  -- hdiv : N/D ≤ (N−x)/(D−x)
  rw [← hN]
  exact hdiv

/-! ### Construction feasibility: B_i ≥ 0 and R_n ≤ 1 -/

/-- V < √(2/3). -/
lemma rudinV_lt_sqrt23 (eps : ℝ) (hOK : rudinOK eps) : rudinV eps < Real.sqrt (2 / 3) := by
  have h1 : rudinV eps < Real.sqrt 3 - 1 := rudinV_lt eps hOK
  have h2 : Real.sqrt 3 - 1 < Real.sqrt (2 / 3) := by
    have hx : 0 ≤ Real.sqrt 3 - 1 := by nlinarith [sqrt3_gt]
    rw [Real.lt_sqrt hx]
    rw [sub_sq, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    nlinarith [sqrt3_gt]
  exact lt_trans h1 h2

/-- V·(1+M) < 1. -/
lemma rudinV_mul_one_add_M_lt_one (eps : ℝ) (hOK : rudinOK eps) :
    rudinV eps * (1 + rudinM eps) < 1 := by
  have hVsqrt : rudinV eps < Real.sqrt (2 / 3) := rudinV_lt_sqrt23 eps hOK
  have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
  have hsq : rudinV eps ^ 2 < 2 / 3 := by
    rw [Real.lt_sqrt (le_of_lt hVpos)] at hVsqrt
    exact hVsqrt
  dsimp [rudinM]
  nlinarith

/-- B_i ≥ 0 on the continuing prefix i < n:
    B_i = S_i(1 − R_i(1+M)) and R_i < V < √(2/3) < 1/(1+M). -/
lemma rudinB_pos_lt_n (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    0 < rudinB eps i := by
  have hB := rudinB_of_lt eps i (rudinN_ratio_lt eps hOK i hi)
  have hpos := rudin_pos_le_n eps hOK i (le_of_lt hi)
  rcases hpos with ⟨hS, hA, hR, hR0⟩
  have hRltV : rudinR eps i < rudinV eps := rudinN_ratio_lt eps hOK i hi
  have hVle : rudinV eps * (1 + rudinM eps) < 1 := rudinV_mul_one_add_M_lt_one eps hOK
  have hmain : rudinR eps i * (1 + rudinM eps) < 1 := by
    have h1 : rudinR eps i * (1 + rudinM eps) ≤ rudinV eps * (1 + rudinM eps) := by
      have hMpos : 0 ≤ 1 + rudinM eps := by nlinarith [rudinM_pos eps hOK]
      exact mul_le_mul_of_nonneg_right (le_of_lt hRltV) hMpos
    exact lt_of_le_of_lt h1 hVle
  rw [hB]
  have hAeq : rudinA eps i = rudinR eps i * rudinS eps i := by
    dsimp [rudinR]
    field_simp [ne_of_gt hS]
  rw [hAeq]
  nlinarith [hS, hmain]

/-! ### Layer separation (Lemma 3.4): runtime tracking -/

/-- The full adversary sequence: all layers n..0 followed by the final job 2A₀. -/
def rudinFullSequence (eps : ℝ) (hOK : rudinOK eps) : JobSequence :=
  rudinPrefixJobs eps (rudinN eps hOK) 0 ++ [2 * rudinA eps 0]

/-- OPT of the B-violation prefix (layers n..i+1 plus two B_i jobs) is at most
    B_i + (3/2)A_{i+1}: put the two B_i jobs on two machines and pack the
    previous layers into 4 parts of load ≤ (3/2)A_{i+1} (Lemma 3.3). -/
lemma rudin_opt_le_B_violation (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i < rudinN eps hOK) :
    OPT (rudinPrefixJobs eps (rudinN eps hOK) i.succ ++
      [rudinB eps i, rudinB eps i]) ≤
      rudinB eps i + 3 / 2 * rudinA eps i.succ := by
  let n := rudinN eps hOK
  have hile : i + 1 ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing eps hOK i.succ hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinB eps i + p4 0
    else if j = 1 then rudinB eps i + p4 1
    else p4 j
  have h4sum' : totalLoad (rudinPrefixJobs eps n i.succ) = ∑ j : Fin 4, p4 j := by
    dsimp [n]
    exact h4sum
  have hsum : totalLoad (rudinPrefixJobs eps n i.succ ++ [rudinB eps i, rudinB eps i]) =
      ∑ j : Fin 4, loads j := by
    rw [show totalLoad (rudinPrefixJobs eps n i.succ ++ [rudinB eps i, rudinB eps i]) =
        totalLoad (rudinPrefixJobs eps n i.succ) + (rudinB eps i + rudinB eps i) by
          simp [totalLoad]]
    rw [h4sum']
    simp [loads, Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinB eps i + 3 / 2 * rudinA eps i.succ := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    by_cases hj0 : j = (0 : Fin 4)
    · subst j
      simp [loads]
      nlinarith [h4le 0, rudinB_pos_lt_n eps hOK i hi]
    · by_cases hj1 : j = (1 : Fin 4)
      · subst j
        simp [loads]
        nlinarith [h4le 1, rudinB_pos_lt_n eps hOK i hi]
      · simp [loads, hj0, hj1]
        nlinarith [h4le j, rudinB_pos_lt_n eps hOK i hi]
  exact le_trans (opt_le_of_schedule (m := 4)
    (rudinPrefixJobs eps n i.succ ++ [rudinB eps i, rudinB eps i]) loads hsum) hmk

/-! ### Clamped construction values (terminal-layer cap) -/

/-- Clamped A_i: at the terminal layer A is capped at S so that B = S − A ≥ 0.
    For i < n this equals the raw A_i. -/
def rudinAC (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) : ℝ :=
  min (rudinA eps i) (rudinS eps i)

/-- Clamped B_i: the raw continuing value for i < n; at the terminal layer
    B_n = S_n − A_n^C = max(S_n − A_n, 0) ≥ 0. -/
def rudinBC (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) : ℝ :=
  if i < rudinN eps hOK then rudinB eps i else rudinS eps i - rudinAC eps hOK i

/-- At the terminal layer, A_n^C + B_n^C = S_n. -/
lemma rudinAC_add_BC_n (eps : ℝ) (hOK : rudinOK eps) :
    rudinAC eps hOK (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK) = rudinS eps (rudinN eps hOK) := by
  dsimp [rudinBC]
  rw [if_neg (not_lt_of_ge (le_rfl : rudinN eps hOK ≤ rudinN eps hOK))]
  ring

/-- B_i^C ≥ 0 on the whole sequence. -/
lemma rudinBC_nonneg (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i ≤ rudinN eps hOK) :
    0 ≤ rudinBC eps hOK i := by
  by_cases hi' : i < rudinN eps hOK
  · rw [rudinBC]
    rw [if_pos hi']
    exact le_of_lt (rudinB_pos_lt_n eps hOK i hi')
  · have hiN : i = rudinN eps hOK := le_antisymm hi (le_of_not_gt hi')
    subst i
    dsimp [rudinBC, rudinAC]
    rw [if_neg (not_lt_of_ge le_rfl)]
    have hm : min (rudinA eps (rudinN eps hOK)) (rudinS eps (rudinN eps hOK)) ≤
        rudinS eps (rudinN eps hOK) := min_le_right _ _
    linarith

/-- V < 1. -/
lemma rudinV_lt_one (eps : ℝ) (hOK : rudinOK eps) : rudinV eps < 1 := by
  have h1 := rudinV_lt_eleven_fifteenth eps hOK
  linarith

/-- A_i < S_i along the continuing path. -/
lemma rudinA_lt_S_of_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    rudinA eps i < rudinS eps i := by
  have hR := rudinN_ratio_lt eps hOK i hi
  have hSpos : 0 < rudinS eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR0, hR00⟩
    exact hS
  have h1 : rudinA eps i / rudinS eps i < 1 :=
    lt_of_lt_of_le hR (le_of_lt (rudinV_lt_one eps hOK))
  have hA : rudinA eps i < rudinS eps i := by
    simpa using (div_lt_iff₀ hSpos).mp h1
  exact hA

/-- On the continuing path the clamped values equal the raw ones. -/
lemma rudinAC_eq_A_of_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    rudinAC eps hOK i = rudinA eps i := by
  dsimp [rudinAC]
  exact min_eq_left (le_of_lt (rudinA_lt_S_of_lt eps hOK i hi))

lemma rudinBC_eq_B_of_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    rudinBC eps hOK i = rudinB eps i := by
  dsimp [rudinBC]
  rw [if_pos hi]

/-- At the terminal layer, A_n^C = min(A_n, S_n) ≥ V·S_n. -/
lemma rudinAC_ge_V_mul_S (eps : ℝ) (hOK : rudinOK eps) :
    rudinV eps * rudinS eps (rudinN eps hOK) ≤ rudinAC eps hOK (rudinN eps hOK) := by
  have hN := rudinN_spec eps hOK
  have hSpos : 0 < rudinS eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have hA : rudinV eps * rudinS eps (rudinN eps hOK) ≤ rudinA eps (rudinN eps hOK) := by
    rw [rudinR] at hN
    exact (le_div_iff₀ hSpos).mp hN
  dsimp [rudinAC]
  exact le_min hA (by nlinarith [hSpos, rudinV_lt_one eps hOK])

/-- The terminal layer satisfies A_n^C ≥ (2/3)·S_n (needed by the packing). -/
lemma rudinAC_ge_two_thirds_S (eps : ℝ) (hOK : rudinOK eps) :
    (2 / 3 : ℝ) * rudinS eps (rudinN eps hOK) ≤ rudinAC eps hOK (rudinN eps hOK) := by
  have hV23 : (2 / 3 : ℝ) ≤ rudinV eps := le_of_lt (rudinV_gt_two_thirds eps hOK)
  have hSpos : 0 < rudinS eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have h1 := rudinAC_ge_V_mul_S eps hOK
  nlinarith [h1, hV23, hSpos]

/-- The terminal layer's ratio is still at least V after clamping. -/
lemma rudinR_n_ge_V (eps : ℝ) (hOK : rudinOK eps) :
    rudinV eps ≤ rudinAC eps hOK (rudinN eps hOK) / rudinS eps (rudinN eps hOK) := by
  have hSpos : 0 < rudinS eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  exact (le_div_iff₀ hSpos).mpr (rudinAC_ge_V_mul_S eps hOK)

/-! ### Clamped layer jobs and packing (Lemma 3.3 for the capped sequence) -/

/-- The four jobs of layer i with the capped values:
    a B-row of four B_i^C and an A-row of three A_i^C plus
    (A_i^C + 2·A_{i+1}^C) (the last layer's A-row is four A_n^C). -/
def rudinLayerJobsC (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) : List ℝ :=
  [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i] ++
  [rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i,
    if i = n then rudinAC eps hOK i else rudinAC eps hOK i + 2 * rudinAC eps hOK i.succ]

/-- The jobs of layers n, n−1, ..., i with the capped values, in that order. -/
def rudinPrefixJobsC (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) : List ℝ :=
  if i ≤ n then rudinLayerJobsC eps hOK n i ++ rudinPrefixJobsC eps hOK n (i + 1) else []
termination_by n + 1 - i
decreasing_by
  omega

lemma rudinPrefixJobsC_eq (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) (hi : i ≤ n) :
    rudinPrefixJobsC eps hOK n i = rudinLayerJobsC eps hOK n i ++ rudinPrefixJobsC eps hOK n (i + 1) := by
  conv =>
    lhs
    unfold rudinPrefixJobsC
  rw [if_pos hi]

lemma rudinPrefixJobsC_succ (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) (hi : i < n) :
    rudinPrefixJobsC eps hOK n i = rudinLayerJobsC eps hOK n i ++ rudinPrefixJobsC eps hOK n (i + 1) :=
  rudinPrefixJobsC_eq eps hOK n i (le_of_lt hi)

/-- Lemma 3.3 for the capped sequence: the jobs of layers n..i can be split into
    4 parts of load ≤ (3/2)·A_i^C and into 3 parts of load ≤ 2·A_i^C. -/
lemma rudin_packing_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i ≤ rudinN eps hOK) :
    (∃ loads : Loads 4, (∀ j : Fin 4, loads j ≤ 3 / 2 * rudinAC eps hOK i) ∧
      totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) i) = ∑ j : Fin 4, loads j) ∧
    (∃ loads : Loads 3, (∀ j : Fin 3, loads j ≤ 2 * rudinAC eps hOK i) ∧
      totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) i) = ∑ j : Fin 3, loads j) := by
  let n := rudinN eps hOK
  let P (i : ℕ) : Prop :=
    (∃ loads : Loads 4, (∀ j : Fin 4, loads j ≤ 3 / 2 * rudinAC eps hOK i) ∧
      totalLoad (rudinPrefixJobsC eps hOK n i) = ∑ j : Fin 4, loads j) ∧
    (∃ loads : Loads 3, (∀ j : Fin 3, loads j ≤ 2 * rudinAC eps hOK i) ∧
      totalLoad (rudinPrefixJobsC eps hOK n i) = ∑ j : Fin 3, loads j)
  have hAC2 : (2 / 3 : ℝ) * rudinS eps n ≤ rudinAC eps hOK n := by
    simpa [n] using rudinAC_ge_two_thirds_S eps hOK
  have hSpos : 0 < rudinS eps n := by
    rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have hbase : P n := by
    dsimp [P]
    constructor
    · refine ⟨fun _ : Fin 4 => rudinBC eps hOK n + rudinAC eps hOK n, ?_⟩
      constructor
      · intro j
        have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
        dsimp [rudinBC]
        rw [if_neg hnot]
        nlinarith [hAC2]
      · have hpref : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
          unfold rudinPrefixJobsC
          rw [if_pos le_rfl]
          unfold rudinPrefixJobsC
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
        rw [hpref]
        simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_four]
        ring
    · refine ⟨fun j : Fin 3 => if j = 0 then 2 * rudinAC eps hOK n
        else rudinAC eps hOK n + 2 * rudinBC eps hOK n, ?_⟩
      constructor
      · intro j
        have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
        fin_cases j <;> simp [rudinBC, if_neg hnot] <;> nlinarith [hAC2]
      · have hpref : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
          unfold rudinPrefixJobsC
          rw [if_pos le_rfl]
          unfold rudinPrefixJobsC
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
        rw [hpref]
        simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_three]
        ring
  have hstep : ∀ k, k + 1 ≤ n → P (n - k) → P (n - (k + 1)) := by
    intro k hk hPk
    let li := n - k
    let li' := n - (k + 1)
    have hli : li = li' + 1 := by dsimp [li, li']; omega
    have hli'le : li' ≤ n := by dsimp [li']; omega
    have hli'lt : li' < n := by dsimp [li']; omega
    have hpref : rudinPrefixJobsC eps hOK n li' =
        rudinLayerJobsC eps hOK n li' ++ rudinPrefixJobsC eps hOK n li := by
      rw [rudinPrefixJobsC_eq eps hOK n li' hli'le]
      rw [← hli]
    rcases hPk with ⟨hP4, hP3⟩
    rcases hP4 with ⟨loads4, h4le, h4sum⟩
    rcases hP3 with ⟨loads3, h3le, h3sum⟩
    -- the key inequality: A_li' ≥ 2·B_li' + 4·A_li^C
    have hAineq : 2 * rudinBC eps hOK li' + 4 * rudinAC eps hOK li ≤ rudinA eps li' := by
      have hraw := rudinA_eq eps li'
      have hsucc : li'.succ = li := by dsimp [li, li']; omega
      rw [hsucc] at hraw
      have hBC : rudinBC eps hOK li' = rudinB eps li' := rudinBC_eq_B_of_lt eps hOK li' hli'lt
      have hAC : rudinAC eps hOK li ≤ rudinA eps li := min_le_left _ _
      rw [hBC]
      nlinarith [hraw, hAC]
    -- new 3-part packing
    let new3 : Loads 3 := fun j =>
      if j = 0 then 2 * rudinAC eps hOK li'
      else if j = 1 then rudinAC eps hOK li' + 2 * rudinBC eps hOK li' + loads3 0 + loads3 1
      else rudinAC eps hOK li' + 2 * rudinAC eps hOK li + 2 * rudinBC eps hOK li' + loads3 2
    have hnew3le : ∀ j : Fin 3, new3 j ≤ 2 * rudinAC eps hOK li' := by
      intro j
      fin_cases j <;> simp [new3, rudinAC_eq_A_of_lt eps hOK li' hli'lt] <;>
        nlinarith [h3le 0, h3le 1, h3le 2, hAineq]
    have hnew3sum : totalLoad (rudinPrefixJobsC eps hOK n li') = ∑ j : Fin 3, new3 j := by
      rw [hpref]
      dsimp [li]
      rw [show totalLoad (rudinLayerJobsC eps hOK n li' ++ rudinPrefixJobsC eps hOK n (n - k)) =
          totalLoad (rudinLayerJobsC eps hOK n li') + totalLoad (rudinPrefixJobsC eps hOK n (n - k)) by
            simp [totalLoad]]
      rw [h3sum]
      simp [Fin.sum_univ_three]
      dsimp [new3]
      simp [rudinLayerJobsC, ne_of_lt hli'lt]
      have hsucc1 : li' + 1 = li := by omega
      rw [hsucc1]
      simp [totalLoad]
      norm_num
      ring
    -- new 4-part packing
    let new4 : Loads 4 := fun j =>
      if h : j.val < 3 then rudinAC eps hOK li' + rudinBC eps hOK li' + loads3 ⟨j.val, h⟩
      else rudinAC eps hOK li' + 2 * rudinAC eps hOK li + rudinBC eps hOK li'
    have hnew4le : ∀ j : Fin 4, new4 j ≤ 3 / 2 * rudinAC eps hOK li' := by
      intro j
      by_cases hj : j.val < 3
      · have hle3 : loads3 ⟨j.val, hj⟩ ≤ 2 * rudinAC eps hOK li := h3le ⟨j.val, hj⟩
        have hB : rudinBC eps hOK li' + 2 * rudinAC eps hOK li ≤ 1 / 2 * rudinA eps li' := by
          nlinarith [hAineq]
        simp [new4, hj, rudinAC_eq_A_of_lt eps hOK li' hli'lt]
        nlinarith [hle3, hB]
      · simp [new4, hj, rudinAC_eq_A_of_lt eps hOK li' hli'lt]
        have hB : rudinBC eps hOK li' + 2 * rudinAC eps hOK li ≤ 1 / 2 * rudinA eps li' := by
          nlinarith [hAineq]
        nlinarith
    have hnew4sum : totalLoad (rudinPrefixJobsC eps hOK n li') = ∑ j : Fin 4, new4 j := by
      rw [hpref]
      dsimp [li]
      rw [show totalLoad (rudinLayerJobsC eps hOK n li' ++ rudinPrefixJobsC eps hOK n (n - k)) =
          totalLoad (rudinLayerJobsC eps hOK n li') + totalLoad (rudinPrefixJobsC eps hOK n (n - k)) by
            simp [totalLoad]]
      rw [h3sum]
      simp [Fin.sum_univ_four, Fin.sum_univ_three]
      dsimp [new4]
      simp [rudinLayerJobsC, ne_of_lt hli'lt]
      have hsucc1 : li' + 1 = li := by omega
      rw [hsucc1]
      simp [totalLoad]
      norm_num
      ring
    constructor
    · exact ⟨new4, hnew4le, hnew4sum⟩
    · exact ⟨new3, hnew3le, hnew3sum⟩
  have hQ : ∀ k, k ≤ n → P (n - k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa [n] using hbase
    | succ k ih =>
        intro hk
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        exact hstep k (by omega) (ih hk')
  have hP : P i := by
    have h := hQ (n - i) (Nat.sub_le n i)
    have h' : n - (n - i) = i := by omega
    simpa [h'] using h
  simpa [n] using hP

/-! ### OPT upper bounds for the capped sequence -/

/-- B-violation OPT for the capped sequence (layers n..i+1 plus two B_i jobs),
    for i + 1 ≤ n − 1 (i.e. the top-adjacent layer is handled separately). -/
lemma rudin_opt_le_B_violation_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i]) ≤
      rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
  let n := rudinN eps hOK
  have hile : i + 1 ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i.succ hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinBC eps hOK i + p4 0
    else if j = 1 then rudinBC eps hOK i + p4 1
    else p4 j
  have h4sum' : totalLoad (rudinPrefixJobsC eps hOK n i.succ) = ∑ j : Fin 4, p4 j := by
    dsimp [n]
    exact h4sum
  have hsum : totalLoad (rudinPrefixJobsC eps hOK n i.succ ++ [rudinBC eps hOK i, rudinBC eps hOK i]) =
      ∑ j : Fin 4, loads j := by
    rw [show totalLoad (rudinPrefixJobsC eps hOK n i.succ ++ [rudinBC eps hOK i, rudinBC eps hOK i]) =
        totalLoad (rudinPrefixJobsC eps hOK n i.succ) + (rudinBC eps hOK i + rudinBC eps hOK i) by
          simp [totalLoad]]
    rw [h4sum']
    simp [loads, Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    have hiN : i ≤ rudinN eps hOK := by omega
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    by_cases hj0 : j = (0 : Fin 4)
    · subst j
      simp [loads]
      have hB : 0 ≤ rudinBC eps hOK i := rudinBC_nonneg eps hOK i hiN
      nlinarith [h4le 0, hB]
    · by_cases hj1 : j = (1 : Fin 4)
      · subst j
        simp [loads]
        have hB : 0 ≤ rudinBC eps hOK i := rudinBC_nonneg eps hOK i hiN
        nlinarith [h4le 1, hB]
      · simp [loads, hj0, hj1]
        have hB : 0 ≤ rudinBC eps hOK i := rudinBC_nonneg eps hOK i hiN
        nlinarith [h4le j, hB]
  exact le_trans (opt_le_of_schedule (m := 4)
    (rudinPrefixJobsC eps hOK n i.succ ++ [rudinBC eps hOK i, rudinBC eps hOK i]) loads hsum) hmk

/-! ### Top-layer ratio bounds and geometric decay -/

/-- The terminal raw ratio R_n never exceeds f(V). -/
lemma rudin_rawR_le_fV (eps : ℝ) (hOK : rudinOK eps) :
    rudinR eps (rudinN eps hOK) ≤ rudin_R_step (rudinV eps) (rudinV eps) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hR_lt : rudinR eps (n - 1) < rudinV eps := by
    dsimp [n]
    exact rudinN_ratio_lt eps hOK (rudinN eps hOK - 1) (by omega)
  have hS : rudinS eps (n - 1) ≠ 0 := by
    intro hz
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    rw [hz] at hS
    linarith
  have hA : rudinA eps (n - 1) ≠ 0 := by
    intro hz
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    rw [hz] at hA
    linarith
  have hRsucc : rudinR eps n = rudin_R_step (rudinV eps) (rudinR eps (n - 1)) := by
    have h := rudinR_succ_of_lt eps hOK (n - 1) hR_lt hS hA
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc] at h
    exact h
  have hmono : rudin_R_step (rudinV eps) (rudinR eps (n - 1)) ≤
      rudin_R_step (rudinV eps) (rudinV eps) := by
    have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
    have hRpos : 0 < rudinR eps (n - 1) := by
      rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
      exact hR
    have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
      intro hz
      apply (ne_of_gt (rudinM_pos eps hOK))
      dsimp [rudinM]
      rw [hz]
      norm_num
    have hsub := rudin_R_step_sub (rudinV eps) (rudinR eps (n - 1)) (rudinV eps)
      hM3 (ne_of_gt hRpos) (ne_of_gt hVpos)
    rw [← sub_nonneg]
    rw [hsub]
    have hM3pos : 0 < 3 * rudinV eps - 2 := by nlinarith [rudinV_gt_two_thirds eps hOK]
    have hden : 0 < 2 * ((3 * rudinV eps - 2) / 2) * rudinV eps * rudinR eps (n - 1) := by
      positivity
    exact div_nonneg (by linarith) (le_of_lt hden)
  rw [hRsucc]
  exact hmono

/-- f(V) ≤ 1/(4M), i.e. V·(1+M) ≤ 1. -/
lemma rudin_fV_le_one_over_fourM (eps : ℝ) (hOK : rudinOK eps) :
    rudin_R_step (rudinV eps) (rudinV eps) ≤ 1 / (4 * rudinM eps) := by
  have hV : rudinV eps ≠ 0 := ne_of_gt (rudinV_pos eps hOK)
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  have h4 : 4 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) ≤ 1 := by
    have hVM : rudinV eps * (1 + rudinM eps) < 1 := rudinV_mul_one_add_M_lt_one eps hOK
    have h4' : 4 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) =
        3 + 2 * rudinM eps - 2 / rudinV eps := by
      dsimp [rudin_R_step]
      rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]
      have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
        intro hz
        apply hM
        dsimp [rudinM]
        rw [hz]
        norm_num
      field_simp [hV, hM3]
      ring
    rw [h4']
    have hmain : 2 + 2 * rudinM eps ≤ 2 / rudinV eps := by
      have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
      rw [le_div_iff₀ hVpos]
      nlinarith [hVM]
    nlinarith [hmain]
  have hMpos4 : 0 < 4 * rudinM eps := by
    have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
    positivity
  rw [le_div_iff₀ hMpos4]
  simpa [mul_comm] using h4

/-- Every ratio on the sequence is at most 1/(4M), so A decays by 1/4 per layer. -/
lemma rudinR_le_one_over_fourM (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i ≤ rudinN eps hOK) : rudinR eps i ≤ 1 / (4 * rudinM eps) := by
  by_cases hz : i < rudinN eps hOK
  · have hR : rudinR eps i < rudinV eps := rudinN_ratio_lt eps hOK i hz
    have hV4 : rudinV eps ≤ 1 / (4 * rudinM eps) := by
      have hMpos4 : 0 < 4 * rudinM eps := by
        have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
        positivity
      rw [le_div_iff₀ hMpos4]
      have hMlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      have hVlt : rudinV eps < 11 / 15 := rudinV_lt_eleven_fifteenth eps hOK
      nlinarith
    exact le_trans (le_of_lt hR) hV4
  · have hi' : i = rudinN eps hOK := le_antisymm hi (le_of_not_gt hz)
    subst i
    exact le_trans (rudin_rawR_le_fV eps hOK) (rudin_fV_le_one_over_fourM eps hOK)

/-- A_{i+1} ≤ A_i/4 along the sequence. -/
lemma rudinA_succ_le_quarter (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ ≤ rudinN eps hOK) : rudinA eps i.succ ≤ 1 / 4 * rudinA eps i := by
  have hA : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_trans (Nat.le_succ i) hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  have hR := rudinR_le_one_over_fourM eps hOK i.succ hi
  have hR4 : 4 * rudinM eps * rudinR eps i.succ ≤ 1 := by
    have hMpos4 : 0 < 4 * rudinM eps := by
      have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
      positivity
    rw [le_div_iff₀ hMpos4] at hR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hR
  have hAeq : rudinA eps i.succ = rudinR eps i.succ * rudinS eps i.succ := by
    dsimp [rudinR]
    have hS' : rudinS eps i.succ ≠ 0 := by
      rw [hS]
      exact mul_ne_zero (ne_of_gt (rudinM_pos eps hOK)) (ne_of_gt hA)
    field_simp [hS']
  rw [hAeq, hS]
  have hM : 0 ≤ rudinM eps := le_of_lt (rudinM_pos eps hOK)
  have hApos : 0 ≤ rudinA eps i := le_of_lt hA
  nlinarith [hR4, hM, hApos]

/-- S_i = A_i + B_i + S_{i+1} along the continuing path. -/
lemma rudinS_eq_add_of_lt (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    rudinS eps i = rudinA eps i + rudinB eps i + rudinS eps i.succ := by
  have hB := rudinB_of_lt eps i (rudinN_ratio_lt eps hOK i hi)
  have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  rw [hB, hS]
  ring

/-- S_n ≤ 2·A_n^C at the terminal layer. -/
lemma rudinS_le_two_AC (eps : ℝ) (hOK : rudinOK eps) :
    rudinS eps (rudinN eps hOK) ≤ 2 * rudinAC eps hOK (rudinN eps hOK) := by
  have hS' : 0 < rudinS eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have hR : 1 / 2 ≤ rudinR eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    have hR0gt : (1 / 2 : ℝ) < rudinR eps 0 := by
      rw [rudinR_zero]
      have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
      rw [lt_div_iff₀ (by positivity : 0 < 2 * rudinV eps)]
      nlinarith [rudinV_lt_one eps hOK]
    nlinarith [hR0, hR0gt]
  by_cases hcl : rudinS eps (rudinN eps hOK) ≤ rudinA eps (rudinN eps hOK)
  · dsimp [rudinAC]
    rw [min_eq_right hcl]
    nlinarith [hS']
  · have hA' : rudinA eps (rudinN eps hOK) < rudinS eps (rudinN eps hOK) := lt_of_not_ge hcl
    dsimp [rudinAC]
    rw [min_eq_left (le_of_lt hA')]
    have hAeq : rudinA eps (rudinN eps hOK) =
        rudinR eps (rudinN eps hOK) * rudinS eps (rudinN eps hOK) := by
      dsimp [rudinR]
      field_simp [ne_of_gt hS']
    rw [hAeq]
    nlinarith [hS', hR]

/-- M·f(V) ≤ 1/4 − M/2, i.e. V·(1+2M) ≤ 1 (equivalent to 3V² − V ≤ 1). -/
lemma rudin_fV_bound (eps : ℝ) (hOK : rudinOK eps) :
    rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) ≤ 1 / 4 - rudinM eps / 2 := by
  have hVsq : rudinV eps ^ 2 < (11 / 15 : ℝ) ^ 2 := by
    exact sq_lt_sq.mpr (by
      rw [abs_of_nonneg (le_of_lt (rudinV_pos eps hOK))]
      rw [abs_of_pos (by norm_num : 0 < (11 / 15 : ℝ))]
      exact rudinV_lt_eleven_fifteenth eps hOK)
  have hV23 : (2 / 3 : ℝ) < rudinV eps := rudinV_gt_two_thirds eps hOK
  have hV1 : 3 * rudinV eps ^ 2 - rudinV eps ≤ 1 := by nlinarith [hVsq, hV23]
  have hV : rudinV eps ≠ 0 := ne_of_gt (rudinV_pos eps hOK)
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  have h4' : 4 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) =
      3 + 2 * rudinM eps - 2 / rudinV eps := by
    dsimp [rudin_R_step]
    rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]
    have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
      intro hz
      apply hM
      dsimp [rudinM]
      rw [hz]
      norm_num
    field_simp [hV, hM3]
    ring
  have hfV4 : 4 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) ≤
      1 - 2 * rudinM eps := by
    rw [h4']
    have hmain : 2 + 4 * rudinM eps ≤ 2 / rudinV eps := by
      have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
      rw [le_div_iff₀ hVpos]
      have hMdef : rudinM eps = (3 * rudinV eps - 2) / 2 := rfl
      nlinarith [hV1, hMdef]
    nlinarith [hmain]
  have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
  nlinarith [hfV4, hMpos]

/-- S_n ≤ B_{n−1} at the top-adjacent layer. -/
lemma rudinS_le_B_pred (eps : ℝ) (hOK : rudinOK eps) :
    rudinS eps (rudinN eps hOK) ≤ rudinB eps (rudinN eps hOK - 1) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hA : 0 < rudinA eps (n - 1) := by
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hS' : 0 < rudinS eps n := by
    rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have hR : rudinR eps n ≤ rudin_R_step (rudinV eps) (rudinV eps) := by
    dsimp [n]
    exact rudin_rawR_le_fV eps hOK
  have hfV : rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) ≤ 1 / 4 - rudinM eps / 2 :=
    rudin_fV_bound eps hOK
  have hSn : rudinS eps n = rudinM eps * rudinA eps (n - 1) := by
    have h := rudinS_succ eps (n - 1)
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc] at h
    exact h
  have hAeq := rudinA_eq eps (n - 1)
  have hAn : rudinA eps n = rudinR eps n * rudinS eps n := by
    dsimp [rudinR]
    field_simp [ne_of_gt hS']
  have hmain : 2 * rudinA eps n ≤ rudinA eps (n - 1) * (1 / 2 - rudinM eps) := by
    have hApos : 0 ≤ rudinA eps (n - 1) := le_of_lt hA
    have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
    rw [hAn, hSn]
    nlinarith [hR, hfV, hApos, hMpos]
  rw [hSn]
  have hB : rudinB eps (n - 1) = rudinA eps (n - 1) / 2 - 2 * rudinA eps n := by
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc] at hAeq
    nlinarith [hAeq]
  rw [hB]
  nlinarith [hmain]

/-- 2·B_n^C ≤ A_n^C at the terminal layer. -/
lemma rudin_two_BC_le_AC (eps : ℝ) (hOK : rudinOK eps) :
    2 * rudinBC eps hOK (rudinN eps hOK) ≤ rudinAC eps hOK (rudinN eps hOK) := by
  have hnot : ¬ rudinN eps hOK < rudinN eps hOK := by omega
  have hSpos : 0 < rudinS eps (rudinN eps hOK) := by
    rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  by_cases hcl : rudinS eps (rudinN eps hOK) ≤ rudinA eps (rudinN eps hOK)
  · dsimp [rudinBC, rudinAC]
    rw [if_neg hnot]
    rw [min_eq_right hcl]
    ring_nf
    exact le_of_lt hSpos
  · have hA' : rudinA eps (rudinN eps hOK) < rudinS eps (rudinN eps hOK) := lt_of_not_ge hcl
    dsimp [rudinBC, rudinAC]
    rw [if_neg hnot]
    rw [min_eq_left (le_of_lt hA')]
    have hR : (2 / 3 : ℝ) ≤ rudinR eps (rudinN eps hOK) := by
      have hV23 : (2 / 3 : ℝ) ≤ rudinV eps := le_of_lt (rudinV_gt_two_thirds eps hOK)
      exact le_trans hV23 (rudinN_spec eps hOK)
    have hAeq : rudinA eps (rudinN eps hOK) =
        rudinR eps (rudinN eps hOK) * rudinS eps (rudinN eps hOK) := by
      dsimp [rudinR]
      field_simp [ne_of_gt hSpos]
    rw [hAeq]
    nlinarith [hSpos, hR]

/-- Total load of the capped prefix of layers n..i is 4·S_i plus the big-job extras,
    bounded by the geometric decay of A. -/
lemma rudin_totalLoad_C_le (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i ≤ rudinN eps hOK) :
    totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) i) ≤
      4 * rudinS eps i + if i < rudinN eps hOK then 8 / 3 * rudinA eps i.succ else 0 := by
  let P : ℕ → Prop := fun d =>
    ∀ j : ℕ, rudinN eps hOK - j = d → j ≤ rudinN eps hOK →
      totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) j) ≤
        4 * rudinS eps j + if j < rudinN eps hOK then 8 / 3 * rudinA eps j.succ else 0
  have hP : ∀ d : ℕ, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro j hdj hle
        by_cases hz : j = rudinN eps hOK
        · subst j
          have hpref : rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) =
              rudinLayerJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) := by
            unfold rudinPrefixJobsC
            rw [if_pos le_rfl]
            unfold rudinPrefixJobsC
            rw [if_neg (by omega : ¬ (rudinN eps hOK) + 1 ≤ rudinN eps hOK)]
            simp
          rw [hpref]
          have hACB : rudinAC eps hOK (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK) =
              rudinS eps (rudinN eps hOK) := rudinAC_add_BC_n eps hOK
          simp [rudinLayerJobsC, totalLoad]
          ring_nf
          nlinarith [hACB]
        · have hlt : j < rudinN eps hOK := lt_of_le_of_ne hle (by intro h; exact hz h)
          have hpref := rudinPrefixJobsC_eq eps hOK (rudinN eps hOK) j (le_of_lt hlt)
          rw [hpref]
          rw [show totalLoad (rudinLayerJobsC eps hOK (rudinN eps hOK) j ++
              rudinPrefixJobsC eps hOK (rudinN eps hOK) (j + 1)) =
              totalLoad (rudinLayerJobsC eps hOK (rudinN eps hOK) j) +
                totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) (j + 1)) by
                simp [totalLoad]]
          have hAC : rudinAC eps hOK j = rudinA eps j := rudinAC_eq_A_of_lt eps hOK j hlt
          have hBC : rudinBC eps hOK j = rudinB eps j := rudinBC_eq_B_of_lt eps hOK j hlt
          have hACn : rudinAC eps hOK j.succ ≤ rudinA eps j.succ := min_le_left _ _
          have hlayer : totalLoad (rudinLayerJobsC eps hOK (rudinN eps hOK) j) ≤
              4 * (rudinA eps j + rudinB eps j) + 2 * rudinA eps j.succ := by
            simp [rudinLayerJobsC, totalLoad, hAC, hBC, if_neg (ne_of_lt hlt)]
            nlinarith [hACn]
          have hle' : j + 1 ≤ rudinN eps hOK := by omega
          have hdiff' : rudinN eps hOK - (j + 1) < d := by
            rw [← hdj]
            omega
          have hrest := ih (rudinN eps hOK - (j + 1)) hdiff' (j + 1) rfl hle'
          have hAn : 0 ≤ rudinA eps j.succ := by
            rcases rudin_pos_le_n eps hOK j.succ hle' with ⟨hS, hA, hR, hR0⟩
            exact le_of_lt hA
          have hS : rudinS eps j = rudinA eps j + rudinB eps j + rudinS eps j.succ :=
            rudinS_eq_add_of_lt eps hOK j hlt
          by_cases hz' : j.succ < rudinN eps hOK
          · have hq := rudinA_succ_le_quarter eps hOK j.succ (by omega)
            have hz1 : j + 1 < rudinN eps hOK := by omega
            simp [hz1] at hrest
            rw [hS]
            simp [hlt]
            nlinarith [hlayer, hrest, hq, hAn]
          · have hz'' : j.succ = rudinN eps hOK := le_antisymm hle' (le_of_not_gt hz')
            have hz1 : j + 1 = rudinN eps hOK := by omega
            simp [hz1] at hrest
            rw [hz''] at hlayer hAn
            rw [hS, hz'', hz1]
            simp [hlt]
            nlinarith [hlayer, hrest, hAn]
  exact hP (rudinN eps hOK - i) i rfl hi

/-- OPT of the A23-violation prefix (layers n..i+1 plus the whole B-row and two A_i
    jobs) is at most A_i + B_i: two machines take (A_i, B_i), one takes 2B_i, and the
    fourth takes all of layers n..i+1 (whose total load is bounded by the geometric
    decay of A: 4·S_{i+1} + 2·ΣA ≤ A_i + B_i since 4M < 1 and A decays by 1/4). -/
lemma rudin_opt_le_A23 (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i]) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
  let n := rudinN eps hOK
  let σ := rudinPrefixJobsC eps hOK n i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i]
  have hAC : rudinAC eps hOK i = rudinA eps i := rudinAC_eq_A_of_lt eps hOK i hi
  have hBC : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i hi
  have hBpos : 0 ≤ rudinB eps i := le_of_lt (rudinB_pos_lt_n eps hOK i hi)
  have hApos : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hA' : 0 ≤ rudinA eps i.succ := by
    rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
    exact le_of_lt hA
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 1 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 2 then 2 * rudinBC eps hOK i
    else totalLoad (rudinPrefixJobsC eps hOK n i.succ)
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    simp [totalLoad, Fin.sum_univ_four]
    ring
  have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
  have hload4 : totalLoad (rudinPrefixJobsC eps hOK n i.succ) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
    have hle' : i.succ ≤ rudinN eps hOK := by dsimp [n]; omega
    have htot := rudin_totalLoad_C_le eps hOK i.succ hle'
    have hq : rudinA eps i.succ ≤ 1 / 4 * rudinA eps i :=
      rudinA_succ_le_quarter eps hOK i hle'
    have hS' : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
    by_cases hz : i.succ < rudinN eps hOK
    · have hq2 : rudinA eps i.succ.succ ≤ 1 / 4 * rudinA eps i.succ :=
        rudinA_succ_le_quarter eps hOK i.succ (by omega)
      rw [hS'] at htot
      simp [hz] at htot
      rw [hAC, hBC]
      dsimp [n]
      nlinarith [htot, hq, hq2, hlt, hApos, hBpos]
    · have hz'' : i.succ = rudinN eps hOK := le_antisymm hle' (le_of_not_gt hz)
      rw [hS', hz''] at htot
      simp [hz''] at htot
      rw [hAC, hBC]
      rw [hz'']
      dsimp [n]
      have hM4 : 4 * rudinM eps * rudinA eps i ≤ rudinA eps i + rudinB eps i := by
        nlinarith [hlt, hApos, hBpos]
      nlinarith [htot, hM4]
  have hmk : makespan 4 loads ≤ rudinAC eps hOK i + rudinBC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
    · simp [loads]
      have hAeq := rudinA_eq eps i
      nlinarith [hBpos, hApos, hA', hBC, hAC, hAeq]
    · simp [loads]
      exact hload4
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- OPT of the B-violation prefix at the top-adjacent layer (layer n plus two
    B_{n−1} jobs) is at most S_n + B_{n−1}: two machines take a full layer-n split
    plus one B_{n−1}, the other two take the layer-n split alone. -/
lemma rudin_opt_le_top_B (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
      List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))) ≤
      rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) := by
  let n := rudinN eps hOK
  let σ := rudinPrefixJobsC eps hOK n n ++
      List.replicate 4 (rudinBC eps hOK (n - 1))
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hBC : rudinBC eps hOK (n - 1) = rudinB eps (n - 1) := by
    dsimp [n]
    exact rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
  have hB : 0 ≤ rudinBC eps hOK (n - 1) := by
    dsimp [n]
    exact rudinBC_nonneg eps hOK (rudinN eps hOK - 1) (by omega)
  let loads : Loads 4 := fun _ => rudinS eps n + rudinBC eps hOK (n - 1)
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    have hpref : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
      unfold rudinPrefixJobsC
      rw [if_pos le_rfl]
      unfold rudinPrefixJobsC
      rw [if_neg (by omega : ¬ n + 1 ≤ n)]
      simp
    rw [hpref]
    have hACB : rudinAC eps hOK n + rudinBC eps hOK n = rudinS eps n := rudinAC_add_BC_n eps hOK
    have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
    simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_four, if_neg hnot]
    ring_nf
    nlinarith [hACB]
  have hmk : makespan 4 loads ≤ rudinS eps n + rudinBC eps hOK (n - 1) := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    simp [loads]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- OPT of the top two layers is at most A_{n−1} + B_{n−1} + 2·A_n^C:
    two machines take (A_{n−1}, B_{n−1}, 2·A_n^C), two take
    (A_{n−1}, B_{n−1}, A_n^C, 2·B_n^C), and one of the latter pair is the big-job
    machine; the bound uses 2·B_n^C ≤ A_n^C. -/
lemma rudin_opt_le_top_A4 (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK - 1)) ≤
      rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
        2 * rudinAC eps hOK (rudinN eps hOK) := by
  let n := rudinN eps hOK
  let σ := rudinPrefixJobsC eps hOK n (n - 1)
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hAC : rudinAC eps hOK (n - 1) = rudinA eps (n - 1) := by
    dsimp [n]
    exact rudinAC_eq_A_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
  have hBC : rudinBC eps hOK (n - 1) = rudinB eps (n - 1) := by
    dsimp [n]
    exact rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
  have hApos : 0 < rudinAC eps hOK (n - 1) := by
    rw [hAC]
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hB : 0 ≤ rudinBC eps hOK (n - 1) := by
    dsimp [n]
    exact rudinBC_nonneg eps hOK (rudinN eps hOK - 1) (by omega)
  have hC : 0 ≤ rudinAC eps hOK n := by
    dsimp [rudinAC]
    exact le_min (le_of_lt (by
      rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
      exact hA)) (le_of_lt (by
      rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
      exact hS))
  have h2BC : 2 * rudinBC eps hOK n ≤ rudinAC eps hOK n := by
    dsimp [n]
    exact rudin_two_BC_le_AC eps hOK
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      2 * rudinAC eps hOK n
    else if j = 1 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else if j = 2 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    have hpref : rudinPrefixJobsC eps hOK n (n - 1) =
        rudinLayerJobsC eps hOK n (n - 1) ++ rudinPrefixJobsC eps hOK n n := by
      rw [rudinPrefixJobsC_eq eps hOK n (n - 1) (by omega)]
      have h1 : 1 ≤ n := by omega
      rw [Nat.sub_add_cancel h1]
    rw [hpref]
    rw [show totalLoad (rudinLayerJobsC eps hOK n (n - 1) ++ rudinPrefixJobsC eps hOK n n) =
        totalLoad (rudinLayerJobsC eps hOK n (n - 1)) + totalLoad (rudinPrefixJobsC eps hOK n n) by
          simp [totalLoad]]
    have hpref2 : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
      unfold rudinPrefixJobsC
      rw [if_pos le_rfl]
      unfold rudinPrefixJobsC
      rw [if_neg (by omega : ¬ n + 1 ≤ n)]
      simp
    rw [hpref2]
    have hne : n - 1 ≠ n := by omega
    have hargrw : rudinAC eps hOK (n - 1 + 1) = rudinAC eps hOK n := by
      congr 1
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_four, hAC, hBC, if_neg hne]
    rw [hargrw]
    ring
  have hmk : makespan 4 loads ≤
      rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-! ### Violation ratio bounds -/

/-- 4M·f(V) = 3 + 2M − 2/V. -/
lemma rudin_fV_mul_4M (eps : ℝ) (hOK : rudinOK eps) :
    4 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) =
      3 + 2 * rudinM eps - 2 / rudinV eps := by
  have hV : rudinV eps ≠ 0 := ne_of_gt (rudinV_pos eps hOK)
  have hM : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
  dsimp [rudin_R_step]
  rw [show rudinM eps = (3 * rudinV eps - 2) / 2 by rfl]
  have hM3 : 3 * rudinV eps - 2 ≠ 0 := by
    intro hz
    apply hM
    dsimp [rudinM]
    rw [hz]
    norm_num
  field_simp [hV, hM3]
  ring

/-- B-violation ratio lower bound: with R = R_{i+1} < V, the violated prefix
    (layers n..i+1 plus two B_i jobs) has ratio ≥ 2(M+1−4MR)/(1−MR). -/
lemma rudin_B_ratio_lb (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i.succ < rudinN eps hOK) :
    2 * (rudinM eps + 1 - 4 * rudinM eps * rudinR eps i.succ) /
        (1 - rudinM eps * rudinR eps i.succ) ≤
      (rudinS eps i.succ + 2 * rudinB eps i) / (rudinB eps i + 3 / 2 * rudinA eps i.succ) := by
  have hA : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hA' : 0 < rudinA eps i.succ := by
    rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hB : 0 < rudinB eps i := rudinB_pos_lt_n eps hOK i (by omega)
  have hden : 0 < rudinB eps i + 3 / 2 * rudinA eps i.succ := by nlinarith [hB, hA']
  have hden' : 0 < 1 - rudinM eps * rudinR eps i.succ := by
    have hR := rudinN_ratio_lt eps hOK i.succ hi
    have hMlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
    have hVlt : rudinV eps < 11 / 15 := rudinV_lt_eleven_fifteenth eps hOK
    have hMpos : 0 < rudinM eps := rudinM_pos eps hOK
    have hRpos : 0 < rudinR eps i.succ := by
      rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
      exact hR
    have hMR : rudinM eps * rudinR eps i.succ < 11 / 150 := by
      nlinarith [hMlt, hVlt, hMpos, hRpos]
    nlinarith [hMR]
  rw [div_le_div_iff₀ hden' hden]
  have hx : rudinM eps * rudinR eps i.succ = rudinA eps i.succ / rudinA eps i := by
    have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
    have hAeq' : rudinA eps i.succ = rudinR eps i.succ * rudinS eps i.succ := by
      dsimp [rudinR]
      have hSne : rudinS eps i.succ ≠ 0 := by
        rw [hS]
        exact mul_ne_zero (ne_of_gt (rudinM_pos eps hOK)) (ne_of_gt hA)
      field_simp [hSne]
    rw [hAeq', hS]
    have hMne : rudinM eps ≠ 0 := ne_of_gt (rudinM_pos eps hOK)
    have hAne : rudinA eps i ≠ 0 := ne_of_gt hA
    field_simp [hMne, hAne]
  have hx' : 4 * rudinM eps * rudinR eps i.succ = 4 * (rudinA eps i.succ / rudinA eps i) := by
    nlinarith [hx]
  have hx1 : 1 - rudinM eps * rudinR eps i.succ = 1 - rudinA eps i.succ / rudinA eps i := by
    nlinarith [hx]
  have hAeq := rudinA_eq eps i
  have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  rw [hS, hx', hx1]
  have hAne : rudinA eps i ≠ 0 := ne_of_gt hA
  field_simp [hAne]
  rw [hAeq]
  nlinarith

/-- Top-adjacent B-violation ratio: 1+V ≤ (S_n + 2B_{n−1})/(S_n + B_{n−1}). -/
lemma rudin_top_B_ratio_ge (eps : ℝ) (hOK : rudinOK eps) :
    1 + rudinV eps ≤ (rudinS eps (rudinN eps hOK) + 2 * rudinB eps (rudinN eps hOK - 1)) /
      (rudinS eps (rudinN eps hOK) + rudinB eps (rudinN eps hOK - 1)) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hA : 0 < rudinA eps (n - 1) := by
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hB : 0 < rudinB eps (n - 1) := rudinB_pos_lt_n eps hOK (n - 1) (by omega)
  have hS' : 0 < rudinS eps n := by
    rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  have hden : 0 < rudinS eps n + rudinB eps (n - 1) := by nlinarith
  rw [le_div_iff₀ hden]
  have hS : rudinS eps n = rudinM eps * rudinA eps (n - 1) := by
    have h := rudinS_succ eps (n - 1)
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc] at h
    exact h
  have hAeq := rudinA_eq eps (n - 1)
  have hAn : rudinA eps n = rudinR eps n * rudinS eps n := by
    dsimp [rudinR]
    field_simp [ne_of_gt hS']
  have hR : rudinR eps n ≤ rudin_R_step (rudinV eps) (rudinV eps) := by
    dsimp [n]
    exact rudin_rawR_le_fV eps hOK
  have hMpos : 0 ≤ rudinM eps := le_of_lt (rudinM_pos eps hOK)
  have hb : 1 / rudinV eps - 1 - rudinM eps ≤ rudinB eps (n - 1) / rudinA eps (n - 1) := by
    have hfV4 := rudin_fV_mul_4M eps hOK
    have hb0 : 1 / rudinV eps - 1 - rudinM eps ≤
        1 / 2 - 2 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) := by
      have h : 1 / 2 - 2 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) =
          1 / rudinV eps - 1 - rudinM eps := by
        have h2 : 2 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) =
            (3 + 2 * rudinM eps - 2 / rudinV eps) / 2 := by
          nlinarith [hfV4]
        rw [h2]
        ring
      rw [h]
    have hB2 : rudinB eps (n - 1) / rudinA eps (n - 1) =
        1 / 2 - 2 * (rudinA eps n / rudinA eps (n - 1)) := by
      have hsucc : (n - 1).succ = n := by omega
      rw [hsucc] at hAeq
      field_simp [ne_of_gt hA]
      nlinarith [hAeq]
    have hAn' : rudinA eps n / rudinA eps (n - 1) = rudinM eps * rudinR eps n := by
      rw [hAn, hS]
      field_simp [ne_of_gt hA]
    have hb1 : 1 / 2 - 2 * rudinM eps * rudin_R_step (rudinV eps) (rudinV eps) ≤
        rudinB eps (n - 1) / rudinA eps (n - 1) := by
      rw [hB2, hAn']
      nlinarith [hR, hMpos]
    exact le_trans hb0 hb1
  have hVsq : rudinV eps ^ 2 + 2 * rudinV eps ≤ 2 := by
    have hVpos : 0 ≤ rudinV eps := le_of_lt (rudinV_pos eps hOK)
    have hVsq2 : rudinV eps ^ 2 < (Real.sqrt 3 - 1) ^ 2 := by
      exact sq_lt_sq.mpr (by
        rw [abs_of_nonneg hVpos]
        rw [abs_of_nonneg (by nlinarith [sqrt3_gt])]
        exact rudinV_lt eps hOK)
    have hsq : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
      rw [sub_sq, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
      ring
    have h2 : 2 * rudinV eps ≤ 2 * (Real.sqrt 3 - 1) := by
      nlinarith [rudinV_lt eps hOK]
    nlinarith [hVsq2, hsq, h2]
  have hb2 : rudinV eps * rudinM eps / (1 - rudinV eps) ≤ 1 / rudinV eps - 1 - rudinM eps := by
    have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
    have h1m : 0 < 1 - rudinV eps := by nlinarith [rudinV_lt_one eps hOK]
    have hVne : rudinV eps ≠ 0 := ne_of_gt hVpos
    have h1mne : 1 - rudinV eps ≠ 0 := ne_of_gt h1m
    field_simp [hVne, h1mne]
    have hMdef : rudinM eps = (3 * rudinV eps - 2) / 2 := rfl
    nlinarith [hVsq, hMdef, hVpos, h1m]
  have hmain : rudinV eps * rudinS eps n ≤ rudinB eps (n - 1) * (1 - rudinV eps) := by
    -- b ≥ 1/V − 1 − M ≥ VM/(1−V) ⟹ B(1−V) ≥ V·M·A = V·S
    have hApos : 0 ≤ rudinA eps (n - 1) := le_of_lt hA
    have h1m : 0 < 1 - rudinV eps := by nlinarith [rudinV_lt_one eps hOK]
    rw [hS]
    have hb2' : rudinV eps * rudinM eps / (1 - rudinV eps) ≤
        rudinB eps (n - 1) / rudinA eps (n - 1) := le_trans hb2 hb
    have hmul : rudinV eps * rudinM eps * rudinA eps (n - 1) ≤
        rudinB eps (n - 1) * (1 - rudinV eps) := by
      rw [div_le_iff₀ h1m] at hb2'
      have hAne : rudinA eps (n - 1) ≠ 0 := ne_of_gt hA
      field_simp [hAne] at hb2'
      exact hb2'
    nlinarith [hmul]
  nlinarith [hmain]

/-- A23 violation ratio: 1+V ≤ (S_{i+1} + B_i + 2A_i)/(A_i + B_i). -/
lemma rudin_A23_ratio_ge_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    1 + rudinV eps ≤ (rudinS eps i.succ + rudinB eps i + 2 * rudinA eps i) /
      (rudinA eps i + rudinB eps i) := by
  have hA : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hB : 0 < rudinB eps i := rudinB_pos_lt_n eps hOK i hi
  have hA' : 0 ≤ rudinA eps i.succ := by
    rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
    exact le_of_lt hA
  have hden : 0 < rudinA eps i + rudinB eps i := by nlinarith
  rw [le_div_iff₀ hden]
  have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  have hAeq := rudinA_eq eps i
  rw [hS]
  have hmain : rudinV eps * rudinB eps i ≤ rudinA eps i * (rudinM eps + 1 - rudinV eps) := by
    have hM : rudinM eps = (3 * rudinV eps - 2) / 2 := rfl
    have hM3 : rudinM eps + 1 - 3 / 2 * rudinV eps = 0 := by nlinarith [hM]
    have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
    nlinarith [hAeq, hA', hM3, hVpos]
  nlinarith [hmain]

/-- A4 violation ratio (fourth A-job collision, i + 1 ≤ n − 1):
    1+V ≤ (S_{i+1} + B_i + 2A_i + 2A_{i+1}) / ((3/2)·A_i). -/
lemma rudin_A4_ratio_ge_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i.succ < rudinN eps hOK) :
    1 + rudinV eps ≤ (rudinS eps i.succ + rudinB eps i + 2 * rudinA eps i +
        2 * rudinA eps i.succ) / (3 / 2 * rudinA eps i) := by
  have hA : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hden : 0 < 3 / 2 * rudinA eps i := by positivity
  rw [le_div_iff₀ hden]
  have heq := rudin_A4_eq eps hOK (rudinA eps i)
  have hS : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  have hAeq := rudinA_eq eps i
  rw [hS]
  have hload : rudinA eps i * (rudinM eps + 5 / 2) ≤
      rudinM eps * rudinA eps i + rudinB eps i + 2 * rudinA eps i + 2 * rudinA eps i.succ := by
    nlinarith [hAeq]
  rw [← heq]
  exact hload

/-- A4 violation ratio at the top-adjacent layer (i = n−1, with the capped A_n^C):
    1+V ≤ (S_n + B_{n−1} + 2A_{n−1} + 2A_n^C) / (A_{n−1} + B_{n−1} + 2A_n^C). -/
lemma rudin_top_A4_ratio_ge (eps : ℝ) (hOK : rudinOK eps) :
    1 + rudinV eps ≤ (rudinS eps (rudinN eps hOK) + rudinB eps (rudinN eps hOK - 1) +
        2 * rudinA eps (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK)) /
      (rudinA eps (rudinN eps hOK - 1) + rudinB eps (rudinN eps hOK - 1) +
        2 * rudinAC eps hOK (rudinN eps hOK)) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hA : 0 < rudinA eps (n - 1) := by
    rcases rudin_pos_le_n eps hOK (n - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hB : 0 < rudinB eps (n - 1) := rudinB_pos_lt_n eps hOK (n - 1) (by omega)
  have hC : 0 ≤ rudinAC eps hOK n := by
    dsimp [rudinAC]
    exact le_min (le_of_lt (by rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩; exact hA))
      (le_of_lt (by rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩; exact hS))
  have hden : 0 < rudinA eps (n - 1) + rudinB eps (n - 1) + 2 * rudinAC eps hOK n := by
    nlinarith [hA, hB, hC]
  rw [le_div_iff₀ hden]
  have hS : rudinS eps n = rudinM eps * rudinA eps (n - 1) := by
    have h := rudinS_succ eps (n - 1)
    have hsucc : (n - 1).succ = n := by omega
    rw [hsucc] at h
    exact h
  have hAeq := rudinA_eq eps (n - 1)
  have hACn : rudinAC eps hOK n ≤ rudinA eps n := min_le_left _ _
  have hM : rudinM eps = (3 * rudinV eps - 2) / 2 := rfl
  have hVpos : 0 < rudinV eps := rudinV_pos eps hOK
  have hsucc : (n - 1).succ = n := by omega
  rw [hsucc] at hAeq
  rw [hS]
  nlinarith [hAeq, hACn, hM, hVpos]

/-! ### Row processing: multiplicities and the split-or-collision dichotomy -/

/-- Running an algorithm on n identical jobs adds a multiple of x to each machine,
    with the multiplicities summing to n. -/
lemma runAlgorithm_append_replicate_counts (n : ℕ) (alg : OnlineAlgorithm 4) (σ : JobSequence)
    (x : ℝ) : ∃ k : Fin 4 → ℕ, (∑ j : Fin 4, k j) = n ∧
      ∀ j : Fin 4, (runAlgorithm 4 alg (σ ++ List.replicate n x)) j =
        (runAlgorithm 4 alg σ) j + (k j : ℝ) * x := by
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · simp
      · intro j
        simp [runAlgorithm]
  | succ n ih =>
      rcases ih with ⟨k, hk_sum, hk⟩
      have hσ : (σ ++ List.replicate (n + 1) x) = (σ ++ List.replicate n x) ++ [x] := by
        rw [List.replicate_succ']
        rw [List.append_assoc]
      let j0 := alg (runAlgorithm 4 alg (σ ++ List.replicate n x)) x
      refine ⟨Function.update k j0 (k j0 + 1), ?_, ?_⟩
      · calc
          (∑ x : Fin 4, Function.update k j0 (k j0 + 1) x)
              = (k j0 + 1) + ∑ x ∈ Finset.univ.erase j0, k x := by
                rw [Finset.sum_update_of_mem (Finset.mem_univ j0)]
                rw [show Finset.univ \ ({j0} : Finset (Fin 4)) = Finset.univ.erase j0 by
                  ext x
                  simp]
          _ = n + 1 := by
                have hback : (∑ x ∈ Finset.univ.erase j0, k x) + k j0 = n := by
                  have h := Finset.sum_erase_add (s := Finset.univ) (a := j0) (f := k) (Finset.mem_univ j0)
                  rw [hk_sum] at h
                  exact h
                omega
      · intro j
        rw [hσ, runAlgorithm_append_singleton]
        dsimp [step]
        by_cases hj : j = alg (runAlgorithm 4 alg (σ ++ List.replicate n x)) x
        · subst j
          rw [show alg (runAlgorithm 4 alg (σ ++ List.replicate n x)) x = j0 by rfl]
          simp
          rw [hk j0]
          ring
        · simp [hj]
          have hjj0 : j ≠ j0 := by
            intro h
            apply hj
            simpa [j0] using h
          simp [hjj0]
          exact hk j

/-- Four identical jobs: either a machine receives at least two of them, or every
    machine receives exactly one. -/
lemma rudin_row_dichotomy_4 (alg : OnlineAlgorithm 4) (σ : JobSequence) (x : ℝ) (hx : 0 ≤ x) :
    (∃ j : Fin 4, (runAlgorithm 4 alg σ) j + 2 * x ≤
      (runAlgorithm 4 alg (σ ++ List.replicate 4 x)) j) ∨
    (∀ j : Fin 4, (runAlgorithm 4 alg (σ ++ List.replicate 4 x)) j =
      (runAlgorithm 4 alg σ) j + x) := by
  rcases runAlgorithm_append_replicate_counts 4 alg σ x with ⟨k, hk_sum, hk⟩
  by_cases hcoll : ∃ j : Fin 4, 2 ≤ k j
  · left
    rcases hcoll with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hk j]
    have hjR : (2 : ℝ) ≤ (k j : ℝ) := by exact_mod_cast hj
    nlinarith [hjR, hx]
  · right
    intro j
    have hle : k j ≤ 1 := by
      by_contra h
      have : 2 ≤ k j := by omega
      exact hcoll ⟨j, this⟩
    have hk1 : k j = 1 := pigeonhole_all_ones (m := 4) k
      (fun i => by
        by_contra h
        have : 2 ≤ k i := by omega
        exact hcoll ⟨i, this⟩) hk_sum j
    rw [hk j, hk1]
    ring

/-- Three identical jobs: either a machine receives at least two of them, or each
    machine receives either none or one. -/
lemma rudin_row_dichotomy_3 (alg : OnlineAlgorithm 4) (σ : JobSequence) (x : ℝ) (hx : 0 ≤ x) :
    (∃ j : Fin 4, (runAlgorithm 4 alg σ) j + 2 * x ≤
      (runAlgorithm 4 alg (σ ++ List.replicate 3 x)) j) ∨
    (∀ j : Fin 4, (runAlgorithm 4 alg (σ ++ List.replicate 3 x)) j =
        (runAlgorithm 4 alg σ) j ∨
      (runAlgorithm 4 alg (σ ++ List.replicate 3 x)) j = (runAlgorithm 4 alg σ) j + x) := by
  rcases runAlgorithm_append_replicate_counts 3 alg σ x with ⟨k, hk_sum, hk⟩
  by_cases hcoll : ∃ j : Fin 4, 2 ≤ k j
  · left
    rcases hcoll with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hk j]
    have hjR : (2 : ℝ) ≤ (k j : ℝ) := by exact_mod_cast hj
    nlinarith [hjR, hx]
  · right
    intro j
    have hle : k j ≤ 1 := by
      by_contra h
      have : 2 ≤ k j := by omega
      exact hcoll ⟨j, this⟩
    by_cases hk0 : k j = 0
    · left
      rw [hk j, hk0]
      ring
    · right
      have hk1 : k j = 1 := by omega
      rw [hk j, hk1]
      ring

/-- OPT of the B-row prefix (layers n..i+1 plus the whole B-row of layer i)
    is at most B_i + (3/2)·A_{i+1}: put one B_i with each of the four packing sets. -/
lemma rudin_opt_le_full_B_row_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i]) ≤
      rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
  let n := rudinN eps hOK
  let σ := rudinPrefixJobsC eps hOK n i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i]
  have hile : i + 1 ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i.succ hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  have hB : 0 ≤ rudinBC eps hOK i := by
    exact rudinBC_nonneg eps hOK i (by omega)
  let loads : Loads 4 := fun j => rudinBC eps hOK i + p4 j
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    simp [σ, loads, totalLoad, Fin.sum_univ_four]
    have h4sum' : (rudinPrefixJobsC eps hOK n (i + 1)).sum = ∑ j : Fin 4, p4 j := by
      have hsucc : i.succ = i + 1 := by omega
      dsimp [n]
      simpa [hsucc, totalLoad] using h4sum
    rw [h4sum']
    simp [Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    simp [loads]
    nlinarith [h4le j, hB]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- OPT of the three-A prefix (layers n..i+1, the whole B-row, and three A_i jobs)
    is at most A_i + B_i: three machines take (A_i, B_i) and the fourth takes the
    remaining B_i together with all of layers n..i+1 (whose total load is ≤ A_i). -/
lemma rudin_opt_le_A3 (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
  let n := rudinN eps hOK
  let σ := rudinPrefixJobsC eps hOK n i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
  have hAC : rudinAC eps hOK i = rudinA eps i := rudinAC_eq_A_of_lt eps hOK i hi
  have hBC : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i hi
  have hB : 0 ≤ rudinBC eps hOK i := by
    exact rudinBC_nonneg eps hOK i (by omega)
  have hApos : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 1 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 2 then rudinAC eps hOK i + rudinBC eps hOK i
    else rudinBC eps hOK i + totalLoad (rudinPrefixJobsC eps hOK n i.succ)
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    simp [σ, loads, totalLoad, Fin.sum_univ_four]
    ring
  have hload4 : rudinBC eps hOK i + totalLoad (rudinPrefixJobsC eps hOK n i.succ) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
    have hle' : i.succ ≤ rudinN eps hOK := by dsimp [n]; omega
    have htot := rudin_totalLoad_C_le eps hOK i.succ hle'
    have hq : rudinA eps i.succ ≤ 1 / 4 * rudinA eps i :=
      rudinA_succ_le_quarter eps hOK i hle'
    have hS' : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
    by_cases hz : i.succ < rudinN eps hOK
    · have hq2 : rudinA eps i.succ.succ ≤ 1 / 4 * rudinA eps i.succ :=
        rudinA_succ_le_quarter eps hOK i.succ (by omega)
      rw [hS'] at htot
      simp [hz] at htot
      rw [hAC, hBC]
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot, hq, hq2, hlt, hApos]
    · have hz'' : i.succ = rudinN eps hOK := le_antisymm hle' (le_of_not_gt hz)
      rw [hS', hz''] at htot
      simp [hz''] at htot
      rw [hAC, hBC]
      rw [hz'']
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot, hlt, hApos]
  have hmk : makespan 4 loads ≤ rudinAC eps hOK i + rudinBC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
    · simp [loads]
    · simp [loads]
      exact hload4
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-! ### Layer separation: runtime tracking -/

/-- Appending on the left preserves prefixes. -/
lemma isPrefix_append_left {α : Type} (p a b : List α) (h : a <+: b) : (p ++ a) <+: (p ++ b) := by
  rcases h with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [List.append_assoc, ht]

/-- Any list is a prefix of itself appended with something. -/
lemma isPrefix_self_append {α : Type} (a b : List α) : a <+: a ++ b := by
  exact ⟨b, rfl⟩

/-- Leading zero jobs do not change the loads. -/
lemma runAlgorithm_zero_prefix (alg : OnlineAlgorithm 4) (σ : JobSequence) :
    runAlgorithm 4 alg (List.replicate 4 0 ++ σ) = runAlgorithm 4 alg σ := by
  rw [runAlgorithm, runAlgorithm, List.foldl_append]
  have hz : (List.replicate 4 0).foldl (step (m := 4) alg) (fun _ : Fin 4 => 0) =
      fun _ : Fin 4 => 0 := by
    simp [step]
  rw [hz]

/-- OPT of the top layer is at most S_n: the split schedule has makespan S_n. -/
lemma rudin_opt_le_layer_n (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK)) ≤
      rudinS eps (rudinN eps hOK) := by
  let n := rudinN eps hOK
  have hpref : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsC
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsC
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  have hACB : rudinAC eps hOK n + rudinBC eps hOK n = rudinS eps n := rudinAC_add_BC_n eps hOK
  have hsum : totalLoad (rudinPrefixJobsC eps hOK n n) = ∑ j : Fin 4, rudinS eps n := by
    rw [hpref]
    have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
    simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_four, if_neg hnot]
    ring_nf
    nlinarith [hACB]
  have hmk : makespan 4 (fun _ : Fin 4 => rudinS eps n) ≤ rudinS eps n := by
    dsimp [makespan]
    exact Finset.sup'_le Finset.univ_nonempty (fun _ => rudinS eps n) (by intro j hj; rfl)
  exact le_trans (opt_le_of_schedule (m := 4) (rudinPrefixJobsC eps hOK n n)
    (fun _ : Fin 4 => rudinS eps n) hsum) hmk

/-- The B-violation ratio chain for i + 1 ≤ n − 1: makespan ≥ (1+V)·OPT. -/
lemma rudin_B_violation_ratio_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK)
    (hmk : rudinS eps i.succ + 2 * rudinBC eps hOK i ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i)))) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i)) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i))) := by
  let σB := rudinPrefixJobsC eps hOK (rudinN eps hOK) i.succ ++
    List.replicate 4 (rudinBC eps hOK i)
  have hR : rudinR eps i.succ < rudinV eps := rudinN_ratio_lt eps hOK i.succ hi
  have hRpos : 0 < rudinR eps i.succ := by
    rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hR
  have hden : 0 < rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    have hB : 0 ≤ rudinBC eps hOK i := rudinBC_nonneg eps hOK i (by omega)
    have hA : 0 < rudinAC eps hOK i.succ := by
      rw [rudinAC_eq_A_of_lt eps hOK i.succ hi]
      rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
      exact hA
    nlinarith
  have hopt : OPT σB ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    dsimp [σB]
    exact rudin_opt_le_full_B_row_C eps hOK i hi
  have h1 := rudin_B_ratio_gt eps hOK (rudinR eps i.succ) hRpos hR
  have h2 := rudin_B_ratio_lb eps hOK i hi
  have h2' : 2 * (rudinM eps + 1 - 4 * rudinM eps * rudinR eps i.succ) /
        (1 - rudinM eps * rudinR eps i.succ) ≤
      (rudinS eps i.succ + 2 * rudinBC eps hOK i) /
        (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) := by
    have hBCi : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i (by omega)
    have hACi : rudinAC eps hOK i.succ = rudinA eps i.succ := rudinAC_eq_A_of_lt eps hOK i.succ hi
    simpa [hBCi, hACi] using h2
  have hratio : 1 + rudinV eps <
      (rudinS eps i.succ + 2 * rudinBC eps hOK i) /
        (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) := lt_of_lt_of_le h1 h2'
  have hprod : (1 + rudinV eps) * (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) ≤
      rudinS eps i.succ + 2 * rudinBC eps hOK i := by
    have hlt := (lt_div_iff₀ hden).mp hratio
    nlinarith
  nlinarith [hmk, hopt, hprod]

/-- The top-adjacent B-violation ratio: makespan ≥ (1+V)·OPT. -/
lemma rudin_top_B_violation_ratio (eps : ℝ) (hOK : rudinOK eps)
    (hmk : rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))))) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1)))) := by
  let σB := rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
    List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))
  have hopt : OPT σB ≤ rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) := by
    dsimp [σB]
    exact rudin_opt_le_top_B eps hOK
  have hratio0 := rudin_top_B_ratio_ge eps hOK
  have hratio : 1 + rudinV eps ≤
      (rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1)) /
        (rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1)) := by
    have hn : 0 < rudinN eps hOK := rudinN_pos eps hOK
    have hBCi : rudinBC eps hOK (rudinN eps hOK - 1) = rudinB eps (rudinN eps hOK - 1) :=
      rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    simpa [hBCi] using hratio0
  have hden : 0 < rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) := by
    have hS : 0 < rudinS eps (rudinN eps hOK) := by
      rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
      exact hS
    have hB : 0 ≤ rudinBC eps hOK (rudinN eps hOK - 1) :=
      rudinBC_nonneg eps hOK (rudinN eps hOK - 1) (by omega)
    nlinarith
  have hprod : (1 + rudinV eps) * (rudinS eps (rudinN eps hOK) +
      rudinBC eps hOK (rudinN eps hOK - 1)) ≤
      rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) := by
    have h := (le_div_iff₀ hden).mp hratio
    nlinarith
  dsimp [σB] at hopt ⊢
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  have h1 : (1 + rudinV eps) * OPT σB ≤
      rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) := by
    dsimp [σB] at hopt ⊢
    have h2 : (1 + rudinV eps) * OPT σB ≤
        (1 + rudinV eps) * (rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1)) := by
      exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
    exact le_trans h2 hprod
  dsimp [σB] at h1 ⊢
  exact le_trans h1 hmk

/-- The top-layer A-collision ratio: a makespan of S_n + A_n^C forces the bound. -/
lemma rudin_top_A_collision_ratio (eps : ℝ) (hOK : rudinOK eps) (alg : OnlineAlgorithm 4)
    (hmk : rudinS eps (rudinN eps hOK) + rudinAC eps hOK (rudinN eps hOK) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK)))) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK)) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK))) := by
  let n := rudinN eps hOK
  have hopt : OPT (rudinPrefixJobsC eps hOK n n) ≤ rudinS eps n := rudin_opt_le_layer_n eps hOK
  have hratio : (1 + rudinV eps) * rudinS eps n ≤ rudinS eps n + rudinAC eps hOK n := by
    have hR := rudinR_n_ge_V eps hOK
    have hS : 0 < rudinS eps n := by
      rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
      exact hS
    have hmain : rudinV eps * rudinS eps n ≤ rudinAC eps hOK n := by
      have hAeq : rudinAC eps hOK n = (rudinAC eps hOK n / rudinS eps n) * rudinS eps n := by
        field_simp [ne_of_gt hS]
      rw [hAeq]
      nlinarith [hR, hS]
    nlinarith [hmain]
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  dsimp [n] at hmk hopt hratio ⊢
  nlinarith [hmk, hopt, hratio, hVpos]

/-- The top layer n: either a violation prefix exists, or every machine has load ≥ S_n. -/
lemma rudin_base_layer_n (eps : ℝ) (hOK : rudinOK eps) (alg : OnlineAlgorithm 4) :
    (∃ σ' : JobSequence, σ' <+: rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) ∧
      algorithmMakespan 4 alg σ' ≥ (1 + rudinV eps) * OPT σ') ∨
    ∀ j : Fin 4, rudinS eps (rudinN eps hOK) ≤
      (runAlgorithm 4 alg (rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK))) j := by
  let n := rudinN eps hOK
  have hpref : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsC
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsC
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  have hAnonneg : 0 ≤ rudinAC eps hOK n := by
    rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
    dsimp [rudinAC]
    exact le_min (le_of_lt hA) (le_of_lt hS)
  have hACB : rudinAC eps hOK n + rudinBC eps hOK n = rudinS eps n := rudinAC_add_BC_n eps hOK
  have hopt_n : OPT (rudinPrefixJobsC eps hOK n n) ≤ rudinS eps n := rudin_opt_le_layer_n eps hOK
  have hV : 1 + rudinV eps ≤ 2 := by nlinarith [rudinV_lt_one eps hOK]
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  have hSpos : 0 < rudinS eps n := by
    rcases rudin_pos_le_n eps hOK n le_rfl with ⟨hS, hA, hR, hR0⟩
    exact hS
  by_cases hBpos : 0 < rudinBC eps hOK n
  · have hBrow := rudin_row_dichotomy_4 alg [] (rudinBC eps hOK n) (le_of_lt hBpos)
    rcases hBrow with hBcoll | hBsplit
    · rcases hBcoll with ⟨j, hj⟩
      left
      refine ⟨List.replicate 4 (rudinBC eps hOK n), ?_, ?_⟩
      · rw [hpref]
        simpa [rudinLayerJobsC] using (isPrefix_self_append
          (List.replicate 4 (rudinBC eps hOK n))
          [rudinAC eps hOK n, rudinAC eps hOK n, rudinAC eps hOK n, rudinAC eps hOK n])
      · have hmk : 2 * rudinBC eps hOK n ≤
            algorithmMakespan 4 alg (List.replicate 4 (rudinBC eps hOK n)) := by
          dsimp [algorithmMakespan]
          have hload : 2 * rudinBC eps hOK n ≤
              (runAlgorithm 4 alg (List.replicate 4 (rudinBC eps hOK n))) j := by
            simpa [runAlgorithm] using hj
          exact le_trans hload (makespan_ge_each (m := 4)
            (runAlgorithm 4 alg (List.replicate 4 (rudinBC eps hOK n))) j)
        have hopt : OPT (List.replicate 4 (rudinBC eps hOK n)) = rudinBC eps hOK n :=
          opt_of_identical_jobs (m := 4) (rudinBC eps hOK n) hBpos
        rw [hopt]
        nlinarith [hmk, hV]
    · let σB := List.replicate 4 (rudinBC eps hOK n)
      have hloads : ∀ j : Fin 4, (runAlgorithm 4 alg σB) j = rudinBC eps hOK n := by
        intro j
        simpa [σB, runAlgorithm] using hBsplit j
      have hArow := rudin_row_dichotomy_4 alg σB (rudinAC eps hOK n) hAnonneg
      rcases hArow with hAcoll | hAsplit
      · rcases hAcoll with ⟨j, hj⟩
        left
        have hmk : rudinS eps n + rudinAC eps hOK n ≤
              algorithmMakespan 4 alg (rudinPrefixJobsC eps hOK n n) := by
            dsimp [algorithmMakespan]
            rw [hpref]
            have hload : rudinBC eps hOK n + 2 * rudinAC eps hOK n ≤
                (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j := by
              have h1 : rudinBC eps hOK n ≤ (runAlgorithm 4 alg σB) j := by
                rw [hloads j]
              have h2 : (runAlgorithm 4 alg σB) j + 2 * rudinAC eps hOK n ≤
                  (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j := by
                simpa [rudinLayerJobsC, σB] using hj
              nlinarith [h1, h2]
            have hbound : rudinS eps n + rudinAC eps hOK n ≤
                rudinBC eps hOK n + 2 * rudinAC eps hOK n := by
              nlinarith [hACB]
            exact le_trans hbound (le_trans hload (makespan_ge_each (m := 4)
              (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j))
        have hratio : (1 + rudinV eps) * rudinS eps n ≤ rudinS eps n + rudinAC eps hOK n := by
          have hR := rudinR_n_ge_V eps hOK
          have hmain : rudinV eps * rudinS eps n ≤ rudinAC eps hOK n := by
            have hAeq : rudinAC eps hOK n = (rudinAC eps hOK n / rudinS eps n) * rudinS eps n := by
              field_simp [ne_of_gt hSpos]
            rw [hAeq]
            nlinarith [hR, hSpos]
          nlinarith [hmain]
        have hRatio : (1 + rudinV eps) * OPT (rudinPrefixJobsC eps hOK n n) ≤
            algorithmMakespan 4 alg (rudinPrefixJobsC eps hOK n n) := by
          nlinarith [hmk, hopt_n, hratio, hVpos]
        refine ⟨rudinPrefixJobsC eps hOK n n, ?_, ?_⟩
        · exact ⟨[], by
            change rudinPrefixJobsC eps hOK n n ++ [] = rudinPrefixJobsC eps hOK n n
            simp⟩
        · exact hRatio
      · right
        intro j
        have hstep := hAsplit j
        have hload : (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j =
            (runAlgorithm 4 alg σB) j + rudinAC eps hOK n := by
          simpa [rudinLayerJobsC, σB] using hstep
        rw [hpref]
        rw [hload, hloads j]
        nlinarith [hACB]
  · have hB0 : rudinBC eps hOK n = 0 := by
      have hBnn : 0 ≤ rudinBC eps hOK n := by
        dsimp [n]
        exact rudinBC_nonneg eps hOK n le_rfl
      nlinarith
    have hArow := rudin_row_dichotomy_4 alg [] (rudinAC eps hOK n) hAnonneg
    rcases hArow with hAcoll | hAsplit
    · rcases hAcoll with ⟨j, hj⟩
      left
      have hmk : 2 * rudinAC eps hOK n ≤ algorithmMakespan 4 alg (rudinPrefixJobsC eps hOK n n) := by
        dsimp [algorithmMakespan]
        rw [hpref]
        have hz : runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n) =
            runAlgorithm 4 alg (List.replicate 4 (rudinAC eps hOK n)) := by
          have hrow : rudinLayerJobsC eps hOK n n =
              List.replicate 4 0 ++ List.replicate 4 (rudinAC eps hOK n) := by
            simp [rudinLayerJobsC, hB0]
          rw [hrow]
          exact runAlgorithm_zero_prefix alg (List.replicate 4 (rudinAC eps hOK n))
        have hload : 2 * rudinAC eps hOK n ≤ (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j := by
          rw [hz]
          simpa [runAlgorithm] using hj
        exact le_trans hload (makespan_ge_each (m := 4)
          (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j)
      have hACeq : rudinAC eps hOK n = rudinS eps n := by nlinarith [hACB, hB0]
      have hRatio : (1 + rudinV eps) * OPT (rudinPrefixJobsC eps hOK n n) ≤
          algorithmMakespan 4 alg (rudinPrefixJobsC eps hOK n n) := by
        nlinarith [hmk, hopt_n, hV, hACeq, hVpos, hSpos]
      refine ⟨rudinPrefixJobsC eps hOK n n, ?_, ?_⟩
      · exact ⟨[], by
          change rudinPrefixJobsC eps hOK n n ++ [] = rudinPrefixJobsC eps hOK n n
          simp⟩
      · exact hRatio
    · right
      intro j
      have hstep := hAsplit j
      have hz : runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n) =
          runAlgorithm 4 alg (List.replicate 4 (rudinAC eps hOK n)) := by
        have hrow : rudinLayerJobsC eps hOK n n =
            List.replicate 4 0 ++ List.replicate 4 (rudinAC eps hOK n) := by
          simp [rudinLayerJobsC, hB0]
        rw [hrow]
        exact runAlgorithm_zero_prefix alg (List.replicate 4 (rudinAC eps hOK n))
      have hload : (runAlgorithm 4 alg (rudinLayerJobsC eps hOK n n)) j = rudinAC eps hOK n := by
        rw [hz]
        simpa [runAlgorithm] using hstep
      rw [hpref]
      rw [hload]
      nlinarith [hACB, hB0]

/-! ### Paper-order prefix and its OPT bounds -/

/-- The jobs of layers n, n−1, ..., i in the paper's processing order (layer n first). -/
def rudinPrefixJobsR (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) : List ℝ :=
  if i ≤ n then rudinPrefixJobsR eps hOK n (i + 1) ++ rudinLayerJobsC eps hOK n i else []
termination_by n + 1 - i
decreasing_by
  omega

lemma rudinPrefixJobsR_eq (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) (hi : i ≤ n) :
    rudinPrefixJobsR eps hOK n i = rudinPrefixJobsR eps hOK n (i + 1) ++ rudinLayerJobsC eps hOK n i := by
  conv =>
    lhs
    unfold rudinPrefixJobsR
  rw [if_pos hi]

/-- The top-layer prefix is the same list in both orders. -/
lemma rudin_prefix_top_R_eq_C (eps : ℝ) (hOK : rudinOK eps) :
    rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) =
      rudinPrefixJobsC eps hOK (rudinN eps hOK) (rudinN eps hOK) := by
  let n := rudinN eps hOK
  have hR : rudinPrefixJobsR eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsR
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsR
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  have hC : rudinPrefixJobsC eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsC
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsC
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  rw [hR, hC]

/-- The reversed prefix has the same total load as the original one. -/
lemma rudin_totalLoad_R_eq_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i ≤ rudinN eps hOK) :
    totalLoad (rudinPrefixJobsR eps hOK (rudinN eps hOK) i) =
      totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) i) := by
  let n := rudinN eps hOK
  have hmain : ∀ d : ℕ, ∀ j : ℕ, n - j = d → j ≤ n →
      totalLoad (rudinPrefixJobsR eps hOK n j) = totalLoad (rudinPrefixJobsC eps hOK n j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro j hdj hle
        by_cases hz : j = n
        · subst j
          rw [rudinPrefixJobsR_eq eps hOK n n (by omega)]
          unfold rudinPrefixJobsR
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
          rw [rudinPrefixJobsC_eq eps hOK n n le_rfl]
          unfold rudinPrefixJobsC
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp [totalLoad]
        · have hlt : j < n := lt_of_le_of_ne hle (by intro h; exact hz h)
          have hle' : j + 1 ≤ n := by omega
          have hdiff' : n - (j + 1) < d := by
            rw [← hdj]
            omega
          have hrest := ih (n - (j + 1)) hdiff' (j + 1) rfl hle'
          rw [rudinPrefixJobsR_eq eps hOK n j (le_of_lt hlt)]
          rw [rudinPrefixJobsC_eq eps hOK n j (le_of_lt hlt)]
          rw [show totalLoad (rudinPrefixJobsR eps hOK n (j + 1) ++ rudinLayerJobsC eps hOK n j) =
              totalLoad (rudinPrefixJobsR eps hOK n (j + 1)) + totalLoad (rudinLayerJobsC eps hOK n j) by
                simp [totalLoad]]
          rw [show totalLoad (rudinLayerJobsC eps hOK n j ++ rudinPrefixJobsC eps hOK n (j + 1)) =
              totalLoad (rudinLayerJobsC eps hOK n j) + totalLoad (rudinPrefixJobsC eps hOK n (j + 1)) by
                simp [totalLoad]]
          rw [hrest]
          rw [show j + 1 = j.succ by omega]
          ring
  have h := hmain (n - i) i rfl hi
  dsimp [n] at h
  exact h

/-- OPT of the top two layers in the paper order is at most A + B + 2·A_n^C. -/
lemma rudin_opt_le_top_A4_R (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK - 1)) ≤
      rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
        2 * rudinAC eps hOK (rudinN eps hOK) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hpref : rudinPrefixJobsR eps hOK n (n - 1) =
      rudinPrefixJobsR eps hOK n n ++ rudinLayerJobsC eps hOK n (n - 1) := by
    rw [rudinPrefixJobsR_eq eps hOK n (n - 1) (by omega)]
    have harg : (n - 1) + 1 = n := by
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    rw [harg]
  have hpref2 : rudinPrefixJobsR eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsR
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsR
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  let σ := rudinPrefixJobsR eps hOK n (n - 1)
  have h2BC : 2 * rudinBC eps hOK n ≤ rudinAC eps hOK n := by
    dsimp [n]
    exact rudin_two_BC_le_AC eps hOK
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      2 * rudinAC eps hOK n
    else if j = 1 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else if j = 2 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ]
    rw [hpref, hpref2]
    have hAC : rudinAC eps hOK (n - 1) = rudinA eps (n - 1) := by
      dsimp [n]
      exact rudinAC_eq_A_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    have hBC : rudinBC eps hOK (n - 1) = rudinB eps (n - 1) := by
      dsimp [n]
      exact rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
    have harg : 1 + (n - 1) = n := by
      have h1 : 1 ≤ n := by omega
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel h1
    have harg2 : (n - 1) + 1 = n := by
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    have hne' : n - 1 ≠ n := by omega
    simp [loads, rudinLayerJobsC, totalLoad, Fin.sum_univ_four, if_neg hnot, if_neg hne', harg, harg2]
    ring
  have hmk : makespan 4 loads ≤
      rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- OPT of the full prefix of layers n..i (paper order) is at most (3/2)·A_i^C
    for i + 1 ≤ n − 1. -/
lemma rudin_opt_le_full_layer_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i) ≤ 3 / 2 * rudinAC eps hOK i := by
  let n := rudinN eps hOK
  have hile : i ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  have hsum : totalLoad (rudinPrefixJobsR eps hOK n i) = ∑ j : Fin 4, p4 j := by
    have htotR : totalLoad (rudinPrefixJobsR eps hOK n i) =
        totalLoad (rudinPrefixJobsC eps hOK n i) := by
      dsimp [n]
      exact rudin_totalLoad_R_eq_C eps hOK i (by simpa [n] using hile)
    rw [htotR]
    dsimp [n]
    simpa [totalLoad] using h4sum
  have hmk : makespan 4 p4 ≤ 3 / 2 * rudinAC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    exact h4le j
  exact le_trans (opt_le_of_schedule (m := 4) (rudinPrefixJobsR eps hOK n i) p4 hsum) hmk

/-- OPT of the B-row prefix (paper order, layers n..i+1 plus the whole B-row of i)
    is at most B_i + (3/2)·A_{i+1} for i + 1 ≤ n − 1. -/
lemma rudin_opt_le_full_B_row_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
      List.replicate 4 (rudinBC eps hOK i)) ≤
      rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
  let n := rudinN eps hOK
  have hile : i + 1 ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i.succ hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  have hB : 0 ≤ rudinBC eps hOK i := by
    dsimp [n] at hile
    exact rudinBC_nonneg eps hOK i (by omega)
  let loads : Loads 4 := fun j => rudinBC eps hOK i + p4 j
  have hsum : totalLoad (rudinPrefixJobsR eps hOK n i.succ ++
      List.replicate 4 (rudinBC eps hOK i)) = ∑ j : Fin 4, loads j := by
    dsimp [loads]
    have htotR : totalLoad (rudinPrefixJobsR eps hOK n (i + 1)) =
        totalLoad (rudinPrefixJobsC eps hOK n (i + 1)) := by
      dsimp [n]
      simpa [show i.succ = i + 1 by omega] using
        (rudin_totalLoad_R_eq_C eps hOK i.succ (by dsimp [n]; omega))
    have htotR' : (rudinPrefixJobsR eps hOK n (i + 1)).sum =
        (rudinPrefixJobsC eps hOK n (i + 1)).sum := by
      simpa [totalLoad] using htotR
    simp [totalLoad]
    rw [htotR']
    have h4sum' : (rudinPrefixJobsC eps hOK n (i + 1)).sum = ∑ j : Fin 4, p4 j := by
      have hsucc : i.succ = i + 1 := by omega
      dsimp [n]
      simpa [hsucc, totalLoad] using h4sum
    rw [h4sum']
    simp [Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    simp [loads]
    nlinarith [h4le j, hB]
  exact le_trans (opt_le_of_schedule (m := 4)
    (rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i)) loads hsum) hmk

/-- OPT of the three-A prefix (paper order) is at most A_i + B_i. -/
lemma rudin_opt_le_A3_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
  let n := rudinN eps hOK
  have hle' : i.succ ≤ rudinN eps hOK := by dsimp [n]; omega
  have htotR : totalLoad (rudinPrefixJobsR eps hOK n i.succ) =
      totalLoad (rudinPrefixJobsC eps hOK n i.succ) := by
    dsimp [n]
    exact rudin_totalLoad_R_eq_C eps hOK i.succ (by dsimp [n]; omega)
  have htot := rudin_totalLoad_C_le eps hOK i.succ hle'
  have hq : rudinA eps i.succ ≤ 1 / 4 * rudinA eps i :=
    rudinA_succ_le_quarter eps hOK i hle'
  have hS' : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  have hAC : rudinAC eps hOK i = rudinA eps i := rudinAC_eq_A_of_lt eps hOK i hi
  have hBC : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i hi
  have hB : 0 ≤ rudinBC eps hOK i := by
    dsimp [n] at hle'
    exact rudinBC_nonneg eps hOK i (by omega)
  have hApos : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hload4 : rudinBC eps hOK i + totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
    by_cases hz : i.succ < rudinN eps hOK
    · have hq2 : rudinA eps i.succ.succ ≤ 1 / 4 * rudinA eps i.succ :=
        rudinA_succ_le_quarter eps hOK i.succ (by omega)
      have htot' : totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤
          4 * rudinS eps i.succ + 8 / 3 * rudinA eps i.succ.succ := by
        rw [htotR]
        rw [hS'] at htot
        simp [hz] at htot
        have hz1 : i + 1 = i.succ := by omega
        rw [← hz1]
        simpa [hS', show rudinN eps hOK = n by rfl] using htot
      rw [hAC, hBC]
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot', hq, hq2, hlt, hApos]
    · have hz'' : i.succ = rudinN eps hOK := le_antisymm hle' (le_of_not_gt hz)
      have htot' : totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤ 4 * rudinS eps i.succ := by
        rw [htotR]
        rw [hS', hz''] at htot
        simp [hz''] at htot
        have hz1 : i + 1 = i.succ := by omega
        have hz1' : i + 1 = rudinN eps hOK := by omega
        rw [hz'']
        have hS2 : 4 * rudinS eps (rudinN eps hOK) = 4 * (rudinM eps * rudinA eps i) := by
          have h := hS'
          rw [hz''] at h
          nlinarith [h]
        rw [hS2]
        simpa [show rudinN eps hOK = n by rfl] using htot
      rw [hAC, hBC]
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot', hlt, hApos]
  let σ := rudinPrefixJobsR eps hOK n i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 1 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 2 then rudinAC eps hOK i + rudinBC eps hOK i
    else rudinBC eps hOK i + totalLoad (rudinPrefixJobsR eps hOK n i.succ)
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    simp [totalLoad, Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinAC eps hOK i + rudinBC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
    · simp [loads]
    · simp [loads]
      exact hload4
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-! ### Layer separation: runtime tracking in the paper order -/

/-- B-violation ratio chain (paper order, i + 1 ≤ n − 1). -/
lemma rudin_B_violation_ratio_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK)
    (hmk : rudinS eps i.succ + 2 * rudinBC eps hOK i ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i)))) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i)) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
        List.replicate 4 (rudinBC eps hOK i))) := by
  let σB := rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++ List.replicate 4 (rudinBC eps hOK i)
  have hR : rudinR eps i.succ < rudinV eps := rudinN_ratio_lt eps hOK i.succ hi
  have hRpos : 0 < rudinR eps i.succ := by
    rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
    exact hR
  have hden : 0 < rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    have hB : 0 ≤ rudinBC eps hOK i := rudinBC_nonneg eps hOK i (by omega)
    have hA : 0 < rudinAC eps hOK i.succ := by
      rw [rudinAC_eq_A_of_lt eps hOK i.succ hi]
      rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
      exact hA
    nlinarith
  have hopt : OPT σB ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    dsimp [σB]
    exact rudin_opt_le_full_B_row_R eps hOK i hi
  have h1 := rudin_B_ratio_gt eps hOK (rudinR eps i.succ) hRpos hR
  have h2 := rudin_B_ratio_lb eps hOK i hi
  have h2' : 2 * (rudinM eps + 1 - 4 * rudinM eps * rudinR eps i.succ) /
        (1 - rudinM eps * rudinR eps i.succ) ≤
      (rudinS eps i.succ + 2 * rudinBC eps hOK i) /
        (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) := by
    have hBCi : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i (by omega)
    have hACi : rudinAC eps hOK i.succ = rudinA eps i.succ := rudinAC_eq_A_of_lt eps hOK i.succ hi
    simpa [hBCi, hACi] using h2
  have hratio : 1 + rudinV eps <
      (rudinS eps i.succ + 2 * rudinBC eps hOK i) /
        (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) := lt_of_lt_of_le h1 h2'
  have hprod : (1 + rudinV eps) * (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) ≤
      rudinS eps i.succ + 2 * rudinBC eps hOK i := by
    have hlt := (lt_div_iff₀ hden).mp hratio
    nlinarith
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  have h1' : (1 + rudinV eps) * OPT σB ≤ rudinS eps i.succ + 2 * rudinBC eps hOK i := by
    have h2'' : (1 + rudinV eps) * OPT σB ≤
        (1 + rudinV eps) * (rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ) := by
      exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
    exact le_trans h2'' hprod
  dsimp [σB] at h1' ⊢
  exact le_trans h1' hmk

/-- Top-adjacent B-violation ratio chain (paper order). -/
lemma rudin_top_B_violation_ratio_R (eps : ℝ) (hOK : rudinOK eps)
    (hmk : rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))))) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))) ≤
      makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
        List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1)))) := by
  let σB := rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
    List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))
  have hopt : OPT σB ≤ rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) := by
    dsimp [σB]
    rw [rudin_prefix_top_R_eq_C]
    exact rudin_opt_le_top_B eps hOK
  have hratio0 := rudin_top_B_ratio_ge eps hOK
  have hratio : 1 + rudinV eps ≤
      (rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1)) /
        (rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1)) := by
    have hn : 0 < rudinN eps hOK := rudinN_pos eps hOK
    have hBCi : rudinBC eps hOK (rudinN eps hOK - 1) = rudinB eps (rudinN eps hOK - 1) :=
      rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    simpa [hBCi] using hratio0
  have hden : 0 < rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) := by
    have hS : 0 < rudinS eps (rudinN eps hOK) := by
      rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
      exact hS
    have hB : 0 ≤ rudinBC eps hOK (rudinN eps hOK - 1) :=
      rudinBC_nonneg eps hOK (rudinN eps hOK - 1) (by omega)
    nlinarith
  have hprod : (1 + rudinV eps) * (rudinS eps (rudinN eps hOK) +
      rudinBC eps hOK (rudinN eps hOK - 1)) ≤
      rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) := by
    have h := (le_div_iff₀ hden).mp hratio
    nlinarith
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  have h1 : (1 + rudinV eps) * OPT σB ≤
      rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) := by
    have h2 : (1 + rudinV eps) * OPT σB ≤
        (1 + rudinV eps) * (rudinS eps (rudinN eps hOK) +
          rudinBC eps hOK (rudinN eps hOK - 1)) := by
      exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
    exact le_trans h2 hprod
  dsimp [σB] at h1 ⊢
  exact le_trans h1 hmk

/-- Processing layer i (i < n) after layers n..i+1: either a violation prefix
    exists, or every machine has load ≥ S_i. -/
lemma rudin_layer_step_R (eps : ℝ) (hOK : rudinOK eps) (alg : OnlineAlgorithm 4) (i : ℕ)
    (hi : i < rudinN eps hOK)
    (hinv : ∀ j : Fin 4, rudinS eps i.succ ≤
      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ)) j) :
    (∃ σ' : JobSequence, σ' <+: rudinPrefixJobsR eps hOK (rudinN eps hOK) i ∧
      algorithmMakespan 4 alg σ' ≥ (1 + rudinV eps) * OPT σ') ∨
    ∀ j : Fin 4, rudinS eps i ≤
      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) i)) j := by
  let n := rudinN eps hOK
  have hpref : rudinPrefixJobsR eps hOK n i =
      rudinPrefixJobsR eps hOK n i.succ ++ rudinLayerJobsC eps hOK n i := by
    rw [rudinPrefixJobsR_eq eps hOK n i (le_of_lt hi)]
  have hB : 0 ≤ rudinBC eps hOK i := by
    exact rudinBC_nonneg eps hOK i (by omega)
  have hBrow := rudin_row_dichotomy_4 alg (rudinPrefixJobsR eps hOK n i.succ) (rudinBC eps hOK i) hB
  rcases hBrow with hBcoll | hBsplit
  · rcases hBcoll with ⟨j, hj⟩
    left
    let σB := rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i)
    have hmk : rudinS eps i.succ + 2 * rudinBC eps hOK i ≤ makespan 4 (runAlgorithm 4 alg σB) := by
      dsimp [σB]
      have hload : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j +
          2 * rudinBC eps hOK i ≤
        (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
          List.replicate 4 (rudinBC eps hOK i))) j := hj
      exact le_trans (by nlinarith [hinv j, hload]) (makespan_ge_each (m := 4)
        (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
          List.replicate 4 (rudinBC eps hOK i))) j)
    have hRatio : (1 + rudinV eps) * OPT σB ≤ makespan 4 (runAlgorithm 4 alg σB) := by
      by_cases htop : i.succ = rudinN eps hOK
      · have hmk' : rudinS eps (rudinN eps hOK) + 2 * rudinBC eps hOK (rudinN eps hOK - 1) ≤
            makespan 4 (runAlgorithm 4 alg
              (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
                List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1)))) := by
          dsimp [σB] at hmk
          rw [show i + 1 = rudinN eps hOK by omega] at hmk
          rw [show i = rudinN eps hOK - 1 by omega] at hmk
          exact hmk
        dsimp [σB]
        rw [show i + 1 = rudinN eps hOK by omega]
        rw [show i = rudinN eps hOK - 1 by omega]
        change (1 + rudinV eps) * OPT
            (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
              List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))) ≤
            makespan 4 (runAlgorithm 4 alg
              (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK) ++
                List.replicate 4 (rudinBC eps hOK (rudinN eps hOK - 1))))
        exact rudin_top_B_violation_ratio_R eps hOK hmk'
      · dsimp [σB]
        exact rudin_B_violation_ratio_R eps hOK i (by omega) hmk
    refine ⟨σB, ?_, hRatio⟩
    rw [hpref]
    exact isPrefix_append_left (rudinPrefixJobsR eps hOK n i.succ)
      (List.replicate 4 (rudinBC eps hOK i)) (rudinLayerJobsC eps hOK n i)
      (by
        simpa [rudinLayerJobsC] using (isPrefix_self_append
          (List.replicate 4 (rudinBC eps hOK i))
          [rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i,
            rudinAC eps hOK i + 2 * rudinAC eps hOK i.succ]))
  · have hBsplit2 : ∀ j : Fin 4, (runAlgorithm 4 alg
        (rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i))) j =
        (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j + rudinBC eps hOK i := by
      intro j
      simpa using hBsplit j
    have hA : 0 ≤ rudinAC eps hOK i := by
      rw [rudinAC_eq_A_of_lt eps hOK i hi]
      rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
      exact le_of_lt hA
    have hArow := rudin_row_dichotomy_3 alg
      (rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i))
      (rudinAC eps hOK i) hA
    rcases hArow with hAcoll | hAsplit
    · rcases hAcoll with ⟨j, hj⟩
      left
      let σA3 := rudinPrefixJobsR eps hOK n i.succ ++
        [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
         rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
      have hmk : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i ≤
          makespan 4 (runAlgorithm 4 alg σA3) := by
        dsimp [σA3]
        have hload : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i ≤
            (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j := by
          nlinarith [hinv j, hBsplit2 j, hj]
        simpa [σA3] using (le_trans hload (makespan_ge_each (m := 4)
          (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
            List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j))
      have hRatio : (1 + rudinV eps) * OPT σA3 ≤ makespan 4 (runAlgorithm 4 alg σA3) := by
        dsimp [σA3]
        have hopt : OPT (rudinPrefixJobsR eps hOK n i.succ ++
            [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
             rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
            rudinAC eps hOK i + rudinBC eps hOK i := rudin_opt_le_A3_R eps hOK i hi
        have hratio := rudin_A23_ratio_ge_C eps hOK i hi
        have hratio' : 1 + rudinV eps ≤
            (rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i) /
              (rudinAC eps hOK i + rudinBC eps hOK i) := by
          simpa [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi] using hratio
        have hden : 0 < rudinAC eps hOK i + rudinBC eps hOK i := by
          have hA' : 0 < rudinA eps i := by
            rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
            exact hA
          have hB' : 0 < rudinB eps i := rudinB_pos_lt_n eps hOK i hi
          rw [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi]
          nlinarith
        have hprod : (1 + rudinV eps) * (rudinAC eps hOK i + rudinBC eps hOK i) ≤
            rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i := by
          have h := (le_div_iff₀ hden).mp hratio'
          nlinarith
        have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
        have h1 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i.succ ++
            [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
             rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
            rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i := by
          have h2 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i.succ ++
              [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
               rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
              (1 + rudinV eps) * (rudinAC eps hOK i + rudinBC eps hOK i) := by
            exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
          exact le_trans h2 hprod
        exact le_trans h1 hmk
      refine ⟨σA3, ?_, hRatio⟩
      rw [hpref]
      exact isPrefix_append_left (rudinPrefixJobsR eps hOK n i.succ)
        [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
         rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
        (rudinLayerJobsC eps hOK n i)
        (by
          simpa [rudinLayerJobsC] using (isPrefix_self_append
            [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
             rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
            [rudinAC eps hOK i + 2 * rudinAC eps hOK i.succ]))
    · have hAcase : ∀ j : Fin 4,
          (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
            List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j ∨
          (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
            List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j + rudinAC eps hOK i := by
        intro j
        simpa using hAsplit j
      let big := rudinAC eps hOK i + 2 * rudinAC eps hOK i.succ
      let σA4 := (rudinPrefixJobsR eps hOK n i.succ ++
        List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i)) ++ [big]
      have hstep := runAlgorithm_append_singleton (m := 4) alg
        (rudinPrefixJobsR eps hOK n i.succ ++
          List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i)) big
      let j0 := alg (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
        List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) big
      by_cases hcoll : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
            List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i
      · left
        have hmk : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
            2 * rudinAC eps hOK i.succ ≤ makespan 4 (runAlgorithm 4 alg σA4) := by
          have hstep' : (runAlgorithm 4 alg σA4) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 + big := by
            rw [show σA4 = (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i)) ++ [big] by rfl]
            rw [hstep]
            dsimp [step, j0]
            simp
          have hload : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i + big ≤
              (runAlgorithm 4 alg σA4) j0 := by
            rw [hstep', hcoll]
          have hbase : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
              2 * rudinAC eps hOK i.succ ≤
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i + big := by
            dsimp [big]
            have hinv' : rudinS eps i.succ ≤
                (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j0 := by
              simpa [n] using hinv j0
            have hBsplit2' : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                  [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i])) j0 =
                  (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j0 + rudinBC eps hOK i := by
              simpa using hBsplit2 j0
            nlinarith [hinv', hB, hBsplit2']
          exact le_trans hbase (le_trans hload (makespan_ge_each (m := 4)
            (runAlgorithm 4 alg σA4) j0))
        have hσ : σA4 = rudinPrefixJobsR eps hOK n i := by
          dsimp [σA4, big]
          rw [hpref]
          have hne : i ≠ n := by omega
          simp [rudinLayerJobsC, if_neg hne]
        have hRatio : (1 + rudinV eps) * OPT σA4 ≤ makespan 4 (runAlgorithm 4 alg σA4) := by
          have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
          by_cases htop : i.succ = rudinN eps hOK
          · have htop' : i + 1 = rudinN eps hOK := by omega
            have hσtop : σA4 = rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1) := by
              rw [hσ]
              rw [show i = rudinN eps hOK - 1 by omega]
            have hopt : OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                  rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
                    2 * rudinAC eps hOK (rudinN eps hOK) := rudin_opt_le_top_A4_R eps hOK
            have hratio := rudin_top_A4_ratio_ge eps hOK
            have hratio' : 1 + rudinV eps ≤
                  (rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) +
                    2 * rudinAC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK)) /
                    (rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
                      2 * rudinAC eps hOK (rudinN eps hOK)) := by
                simpa [rudinAC_eq_A_of_lt eps hOK (rudinN eps hOK - 1) (by omega),
                  rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)] using hratio
            have hden : 0 < rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
                  2 * rudinAC eps hOK (rudinN eps hOK) := by
              have hA' : 0 < rudinA eps (rudinN eps hOK - 1) := by
                rcases rudin_pos_le_n eps hOK (rudinN eps hOK - 1) (by omega) with ⟨hS, hA, hR, hR0⟩
                exact hA
              have hB' : 0 < rudinB eps (rudinN eps hOK - 1) :=
                rudinB_pos_lt_n eps hOK (rudinN eps hOK - 1) (by omega)
              have hC : 0 ≤ rudinAC eps hOK (rudinN eps hOK) := by
                rcases rudin_pos_le_n eps hOK (rudinN eps hOK) le_rfl with ⟨hS, hA, hR, hR0⟩
                dsimp [rudinAC]
                exact le_min (le_of_lt hA) (le_of_lt hS)
              rw [rudinAC_eq_A_of_lt eps hOK (rudinN eps hOK - 1) (by omega),
                rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)]
              nlinarith
            have hprod : (1 + rudinV eps) * (rudinAC eps hOK (rudinN eps hOK - 1) +
                    rudinBC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK)) ≤
                  rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) +
                    2 * rudinAC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK) := by
                have h := (le_div_iff₀ hden).mp hratio'
                nlinarith
            have h1 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                  rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) +
                    2 * rudinAC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK) := by
              have h2 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                    (1 + rudinV eps) * (rudinAC eps hOK (rudinN eps hOK - 1) +
                      rudinBC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK)) := by
                  exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
              exact le_trans h2 hprod
            have hmk' : rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) +
                    2 * rudinAC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK) ≤
                  makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1))) := by
              rw [← hσtop]
              simpa [show i = rudinN eps hOK - 1 by omega,
                show (rudinN eps hOK - 1) + 1 = rudinN eps hOK by omega] using hmk
            rw [← hσtop] at h1 hmk'
            exact le_trans h1 hmk'
          · have h1 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i) ≤
                  rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                    2 * rudinAC eps hOK i.succ := by
                have hopt : OPT (rudinPrefixJobsR eps hOK n i) ≤ 3 / 2 * rudinAC eps hOK i :=
                  rudin_opt_le_full_layer_R eps hOK i (by omega)
                have hratio := rudin_A4_ratio_ge_C eps hOK i (by omega)
                have hratio' : 1 + rudinV eps ≤
                      (rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                        2 * rudinAC eps hOK i.succ) / (3 / 2 * rudinAC eps hOK i) := by
                    simpa [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi,
                      rudinAC_eq_A_of_lt eps hOK i.succ (by omega)] using hratio
                have hden : 0 < 3 / 2 * rudinAC eps hOK i := by
                  have hA' : 0 < rudinA eps i := by
                    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
                    exact hA
                  rw [rudinAC_eq_A_of_lt eps hOK i hi]
                  positivity
                have hprod : (1 + rudinV eps) * (3 / 2 * rudinAC eps hOK i) ≤
                      rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                        2 * rudinAC eps hOK i.succ := by
                    have h := (le_div_iff₀ hden).mp hratio'
                    nlinarith
                have h2 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i) ≤
                      (1 + rudinV eps) * (3 / 2 * rudinAC eps hOK i) := by
                    exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
                exact le_trans h2 hprod
            have hmk' : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                    2 * rudinAC eps hOK i.succ ≤
                  makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i)) := by
              rw [← hσ]
              simpa [show rudinN eps hOK = n by rfl] using hmk
            rw [← hσ] at h1 hmk'
            exact le_trans h1 hmk'
        refine ⟨σA4, ?_, hRatio⟩
        rw [hσ]
      · right
        intro j
        have hσ : σA4 = rudinPrefixJobsR eps hOK n i := by
          dsimp [σA4, big]
          rw [hpref]
          have hne : i ≠ n := by omega
          simp [rudinLayerJobsC, if_neg hne]
        by_cases hj : j = j0
        · subst j
          have hload : (runAlgorithm 4 alg σA4) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 + big := by
            simp only [σA4, j0]
            rw [hstep]
            dsimp [step]
            simp
          have hfresh : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j0 := by
            by_cases hc : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                  List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                  (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                    List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i
            · exfalso
              exact hcoll hc
            · have hplain : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                    List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                    (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                      List.replicate 4 (rudinBC eps hOK i))) j0 := by
                rcases hAcase j0 with hp | hq
                · exact hp
                · exact (False.elim (hc hq))
              exact hplain
          have hA' : 0 ≤ rudinAC eps hOK i.succ := by
            dsimp [rudinAC]
            exact le_min (le_of_lt (rudin_pos_le_n eps hOK i.succ (Nat.succ_le_of_lt hi)).2.1)
              (le_of_lt (rudin_pos_le_n eps hOK i.succ (Nat.succ_le_of_lt hi)).1)
          have hSi : rudinS eps i = rudinS eps i.succ + rudinBC eps hOK i + rudinAC eps hOK i := by
            have hS' : rudinS eps i = rudinA eps i + rudinB eps i + rudinS eps i.succ :=
              rudinS_eq_add_of_lt eps hOK i hi
            rw [hS']
            rw [← rudinAC_eq_A_of_lt eps hOK i hi, ← rudinBC_eq_B_of_lt eps hOK i hi]
            ring
          rw [← hσ]
          rw [hload, hfresh]
          dsimp [big]
          rw [hSi]
          have hinv0 : rudinS eps i.succ ≤
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j0 := by
            simpa [n] using hinv j0
          have hBsplit2' : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i])) j0 =
                (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ)) j0 + rudinBC eps hOK i := by
            simpa using hBsplit2 j0
          nlinarith [hinv0, hBsplit2', hA']
        · rcases runAlgorithm_append_replicate_counts 3 alg
            (rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i))
            (rudinAC eps hOK i) with ⟨k, hk_sum, hk⟩
          have hk_le : ∀ jj : Fin 4, k jj ≤ 1 := by
            intro jj
            by_contra h
            have hge : 2 ≤ k jj := by omega
            have hApos : 0 < rudinAC eps hOK i := by
              rw [rudinAC_eq_A_of_lt eps hOK i hi]
              rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
              exact hA
            have hbig : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) jj ≥
                (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                  List.replicate 4 (rudinBC eps hOK i))) jj + 2 * rudinAC eps hOK i := by
              rw [hk jj]
              have hgeR : (2 : ℝ) ≤ (k jj : ℝ) := by exact_mod_cast hge
              have hprod : 2 * rudinAC eps hOK i ≤ (k jj : ℝ) * rudinAC eps hOK i := by
                exact mul_le_mul_of_nonneg_right hgeR (le_of_lt hApos)
              nlinarith [hprod]
            rcases (hAcase jj) with hAcase | hBcase
            · rw [hAcase] at hbig
              have hgeR : (2 : ℝ) ≤ (k jj : ℝ) := by exact_mod_cast hge
              have hprod : 2 * rudinAC eps hOK i ≤ (k jj : ℝ) * rudinAC eps hOK i := by
                exact mul_le_mul_of_nonneg_right hgeR (le_of_lt hApos)
              nlinarith [hbig, hprod]
            · rw [hBcase] at hbig
              have hgeR : (2 : ℝ) ≤ (k jj : ℝ) := by exact_mod_cast hge
              have hprod : 2 * rudinAC eps hOK i ≤ (k jj : ℝ) * rudinAC eps hOK i := by
                exact mul_le_mul_of_nonneg_right hgeR (le_of_lt hApos)
              nlinarith [hbig, hprod]
          have hk_j0 : k j0 = 0 := by
            have h1 := hk j0
            have h2 : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                  List.replicate 4 (rudinBC eps hOK i))) j0 := by
              by_cases hc : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                    List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                    (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                      List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i
              · exfalso
                exact hcoll hc
              · have hplain : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                      List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                        List.replicate 4 (rudinBC eps hOK i))) j0 := by
                  rcases (hAcase j0) with hp | hq
                  · exact hp
                  · exact (False.elim (hc hq))
                exact hplain
            have hApos : 0 < rudinAC eps hOK i := by
              rw [rudinAC_eq_A_of_lt eps hOK i hi]
              rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
              exact hA
            have hk0R : (k j0 : ℝ) = 0 := by
              nlinarith [h1, h2, hApos]
            exact_mod_cast hk0R
          have hk_j : k j = 1 := by
            by_contra h
            have hk0 : k j = 0 := by
              by_cases hz : k j = 0
              · exact hz
              · exfalso
                have hlej : k j ≤ 1 := hk_le j
                omega
            have hne : j ≠ j0 := by
              intro hz
              exact hj hz
            have hsum_le2 : (∑ x : Fin 4, k x) ≤ 2 := by
              have hbnd : ∀ x : Fin 4, k x ≤ (if x = j ∨ x = j0 then 0 else 1 : ℕ) := by
                intro x
                by_cases h1 : x = j
                · subst x
                  simp [hk0]
                · by_cases h2 : x = j0
                  · subst x
                    simp [hk_j0]
                  · have hle : k x ≤ 1 := hk_le x
                    simp [h1, h2, hle]
              have hsum_ind : (∑ x : Fin 4, (if x = j ∨ x = j0 then 0 else 1 : ℕ)) = 2 := by
                exact rudin_sum_indicator_two j j0 hne
              calc
                (∑ x : Fin 4, k x) ≤ (∑ x : Fin 4, (if x = j ∨ x = j0 then 0 else 1 : ℕ)) := by
                  exact Finset.sum_le_sum (fun x hx => hbnd x)
                _ = 2 := hsum_ind
            nlinarith [hsum_le2, hk_sum]
          have hloadsA : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j + rudinAC eps hOK i := by
            rw [hk j, hk_j]
            ring
          have hload' : (runAlgorithm 4 alg σA4) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j := by
            simp only [σA4, j0]
            rw [hstep]
            dsimp [step]
            dsimp [j0] at hj
            rw [if_neg hj]
          have hSi : rudinS eps i = rudinS eps i.succ + rudinBC eps hOK i + rudinAC eps hOK i := by
            have hS' : rudinS eps i = rudinA eps i + rudinB eps i + rudinS eps i.succ :=
              rudinS_eq_add_of_lt eps hOK i hi
            rw [hS']
            rw [← rudinAC_eq_A_of_lt eps hOK i hi, ← rudinBC_eq_B_of_lt eps hOK i hi]
            ring
          rw [← hσ]
          rw [hload', hloadsA]
          rw [hSi]
          nlinarith [hinv j, hBsplit2 j]

/-- Layer separation (Lemma 3.4): on the paper-order sequence, either a prefix
    forces the ratio 1+V, or every machine has load ≥ S₀ after all layers. -/
theorem rudin_layer_separation (eps : ℝ) (hOK : rudinOK eps) (alg : OnlineAlgorithm 4) :
    (∃ σ' : JobSequence, σ' <+: rudinPrefixJobsR eps hOK (rudinN eps hOK) 0 ∧
      algorithmMakespan 4 alg σ' ≥ (1 + rudinV eps) * OPT σ') ∨
    ∀ j : Fin 4, rudinS eps 0 ≤
      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) 0)) j := by
  let P (i : ℕ) : Prop :=
    (∃ σ' : JobSequence, σ' <+: rudinPrefixJobsR eps hOK (rudinN eps hOK) i ∧
      algorithmMakespan 4 alg σ' ≥ (1 + rudinV eps) * OPT σ') ∨
    ∀ j : Fin 4, rudinS eps i ≤
      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) i)) j
  have hbase : P (rudinN eps hOK) := by
    dsimp [P]
    rw [rudin_prefix_top_R_eq_C]
    exact rudin_base_layer_n eps hOK alg
  have hstep : ∀ i : ℕ, i < rudinN eps hOK → P i.succ → P i := by
    intro i hi hP
    rcases hP with hviol | hsplit
    · left
      rcases hviol with ⟨σ', hpref', hv⟩
      refine ⟨σ', ?_, hv⟩
      exact List.IsPrefix.trans hpref' (by
        rw [rudinPrefixJobsR_eq eps hOK (rudinN eps hOK) i (le_of_lt hi)]
        exact isPrefix_self_append (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ)
          (rudinLayerJobsC eps hOK (rudinN eps hOK) i))
    · have hstep' := rudin_layer_step_R eps hOK alg i hi hsplit
      rcases hstep' with hviol' | hsplit'
      · left
        exact hviol'
      · right
        exact hsplit'
  have hP0 : P 0 := by
    let Q (d : ℕ) : Prop := ∀ i : ℕ, rudinN eps hOK - i = d → i ≤ rudinN eps hOK → P i
    have hQ : ∀ d : ℕ, Q d := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
          intro i hdi hle
          by_cases hz : i = rudinN eps hOK
          · subst i
            exact hbase
          · have hlt : i < rudinN eps hOK := lt_of_le_of_ne hle (by intro h; exact hz h)
            have hle' : i.succ ≤ rudinN eps hOK := by omega
            have hdiff' : rudinN eps hOK - i.succ < d := by
              rw [← hdi]
              omega
            have hPsucc := ih (rudinN eps hOK - i.succ) hdiff' i.succ rfl hle'
            exact hstep i hlt hPsucc
    exact hQ (rudinN eps hOK - 0) 0 (by simp) (by omega)
  exact hP0

/-- OPT of the full sequence (layers plus the final job 2A₀) is at most 2·A₀. -/
lemma rudin_opt_le_final_R (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) 0 ++ [2 * rudinAC eps hOK 0]) ≤
      2 * rudinAC eps hOK 0 := by
  let n := rudinN eps hOK
  have hpack := rudin_packing_C eps hOK 0 (by omega)
  rcases hpack.2 with ⟨p3, h3le, h3sum⟩
  have htotR : totalLoad (rudinPrefixJobsR eps hOK n 0) =
      totalLoad (rudinPrefixJobsC eps hOK n 0) := by
    dsimp [n]
    exact rudin_totalLoad_R_eq_C eps hOK 0 (by omega)
  let σ := rudinPrefixJobsR eps hOK n 0 ++ [2 * rudinAC eps hOK 0]
  let loads : Loads 4 := fun j => if h : j.val < 3 then p3 ⟨j.val, h⟩ else 2 * rudinAC eps hOK 0
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    change (rudinPrefixJobsR eps hOK n 0 ++ [2 * rudinAC eps hOK 0]).sum =
      ∑ j : Fin 4, loads j
    rw [List.sum_append]
    rw [show (rudinPrefixJobsR eps hOK n 0).sum = (rudinPrefixJobsC eps hOK n 0).sum by
      simpa [totalLoad] using htotR]
    have h3sum' : (rudinPrefixJobsC eps hOK n 0).sum = ∑ j : Fin 3, p3 j := by
      dsimp [n]
      simpa [totalLoad] using h3sum
    simp [loads, h3sum', Fin.sum_univ_four, Fin.sum_univ_three]
  have hmk : makespan 4 loads ≤ 2 * rudinAC eps hOK 0 := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    by_cases hj3 : j.val < 3
    · simp [loads, hj3]
      exact h3le ⟨j.val, hj3⟩
    · simp [loads, hj3]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- Lemma 3.5: the final job 2A₀ forces the ratio when every machine has load ≥ S₀. -/
lemma rudin_final_job_forces (eps : ℝ) (hOK : rudinOK eps) (alg : OnlineAlgorithm 4)
    (hinv : ∀ j : Fin 4, rudinS eps 0 ≤
      (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) 0)) j) :
    (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) 0 ++
        [2 * rudinAC eps hOK 0]) ≤
      algorithmMakespan 4 alg (rudinPrefixJobsR eps hOK (rudinN eps hOK) 0 ++
        [2 * rudinAC eps hOK 0]) := by
  let σ := rudinPrefixJobsR eps hOK (rudinN eps hOK) 0
  have hopt : OPT (σ ++ [2 * rudinAC eps hOK 0]) ≤ 2 * rudinAC eps hOK 0 := by
    dsimp [σ]
    exact rudin_opt_le_final_R eps hOK
  have hstep := runAlgorithm_append_singleton (m := 4) alg σ (2 * rudinAC eps hOK 0)
  let j0 := alg (runAlgorithm 4 alg σ) (2 * rudinAC eps hOK 0)
  have hmk0 : rudinS eps 0 + 2 * rudinAC eps hOK 0 ≤
      makespan 4 (runAlgorithm 4 alg (σ ++ [2 * rudinAC eps hOK 0])) := by
    have hload : (runAlgorithm 4 alg σ) j0 + 2 * rudinAC eps hOK 0 ≤
        (runAlgorithm 4 alg (σ ++ [2 * rudinAC eps hOK 0])) j0 := by
      rw [hstep]
      dsimp [j0]
      dsimp [step]
      simp
    exact le_trans (by nlinarith [hinv j0]) (le_trans hload (makespan_ge_each (m := 4)
      (runAlgorithm 4 alg (σ ++ [2 * rudinAC eps hOK 0])) j0))
  have hA0V : 2 * rudinAC eps hOK 0 * rudinV eps = 1 := by
    have h0 : 0 < rudinN eps hOK := rudinN_pos eps hOK
    have hA : rudinAC eps hOK 0 = rudinA eps 0 := rudinAC_eq_A_of_lt eps hOK 0 (by omega)
    rw [hA, rudinA_zero]
    have hV : rudinV eps ≠ 0 := ne_of_gt (rudinV_pos eps hOK)
    field_simp [hV]
  have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
  have hS0 : rudinS eps 0 = 1 := rudinS_zero eps
  have hmain : (1 + rudinV eps) * (2 * rudinAC eps hOK 0) ≤
      rudinS eps 0 + 2 * rudinAC eps hOK 0 := by
    rw [hS0]
    nlinarith [hA0V]
  have h1 : (1 + rudinV eps) * OPT (σ ++ [2 * rudinAC eps hOK 0]) ≤
      rudinS eps 0 + 2 * rudinAC eps hOK 0 := by
    have h2 : (1 + rudinV eps) * OPT (σ ++ [2 * rudinAC eps hOK 0]) ≤
        (1 + rudinV eps) * (2 * rudinAC eps hOK 0) := by
      exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
    exact le_trans h2 hmain
  exact le_trans h1 hmk0

/-- The adversary: for every ε > 0 the construction forces a ratio ≥ √3 − ε. -/
theorem rudin_m4_adversary_exists (epsilon : ℝ) (heps_pos : 0 < epsilon)
    (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence,
      algorithmMakespan 4 alg sigma ≥ (Real.sqrt 3 - epsilon) * OPT sigma := by
  let eps' := min epsilon (1 / 200 : ℝ)
  have hOK : rudinOK eps' := by
    dsimp [eps', rudinOK]
    constructor
    · exact lt_min heps_pos (by norm_num)
    · exact lt_of_le_of_lt (min_le_right epsilon (1 / 200 : ℝ)) (by norm_num)
  rcases rudin_layer_separation eps' hOK alg with hviol | hsplit
  · rcases hviol with ⟨σ', hpref', hv⟩
    refine ⟨σ', ?_⟩
    have hV : 1 + rudinV eps' = Real.sqrt 3 - eps' := by dsimp [rudinV]; ring
    have hle : Real.sqrt 3 - epsilon ≤ Real.sqrt 3 - eps' := by
      have hmin : eps' ≤ epsilon := min_le_left epsilon (1 / 200 : ℝ)
      nlinarith
    have h1 : (Real.sqrt 3 - epsilon) * OPT σ' ≤ (1 + rudinV eps') * OPT σ' := by
      rw [hV]
      exact mul_le_mul_of_nonneg_right hle (rudin_opt_nonneg σ')
    nlinarith [hv, h1]
  · refine ⟨rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
      [2 * rudinAC eps' hOK 0], ?_⟩
    have hf := rudin_final_job_forces eps' hOK alg hsplit
    have hV : 1 + rudinV eps' = Real.sqrt 3 - eps' := by dsimp [rudinV]; ring
    have hle : Real.sqrt 3 - epsilon ≤ Real.sqrt 3 - eps' := by
      have hmin : eps' ≤ epsilon := min_le_left epsilon (1 / 200 : ℝ)
      nlinarith
    have hOPTpos : 0 ≤ OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
        [2 * rudinAC eps' hOK 0]) := rudin_opt_nonneg _
    -- makespan ≥ (1+V(ε'))·OPT = (√3−ε')·OPT ≥ (√3−ε)·OPT
    have h1 : (1 + rudinV eps') * OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
        [2 * rudinAC eps' hOK 0]) ≤
        algorithmMakespan 4 alg (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
          [2 * rudinAC eps' hOK 0]) := hf
    have h2 : (Real.sqrt 3 - epsilon) * OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
        [2 * rudinAC eps' hOK 0]) ≤
        (1 + rudinV eps') * OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
          [2 * rudinAC eps' hOK 0]) := by
      rw [hV]
      exact mul_le_mul_of_nonneg_right hle hOPTpos
    nlinarith [h1, h2]

theorem rudin_m4_lower_bound (epsilon : ℝ) (heps_pos : 0 < epsilon)
    (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence,
      algorithmMakespan 4 alg sigma ≥ (Real.sqrt 3 - epsilon) * OPT sigma :=
  rudin_m4_adversary_exists epsilon heps_pos alg

axiom rudin_asymptotic_adversary_exists (m : Nat) [NeZero m]
    (hm : 3454 ≤ m) (alg : OnlineAlgorithm m) :
    ∃ sigma : JobSequence,
      algorithmMakespan m alg sigma ≥ rudin_asymptotic * OPT sigma

theorem rudin_asymptotic_lower_bound (m : Nat) [NeZero m]
    (hm : m ≥ 3454) (alg : OnlineAlgorithm m) :
    ∃ sigma : JobSequence,
      algorithmMakespan m alg sigma ≥ rudin_asymptotic * OPT sigma :=
  rudin_asymptotic_adversary_exists m hm alg

end

end OnlineScheduling
