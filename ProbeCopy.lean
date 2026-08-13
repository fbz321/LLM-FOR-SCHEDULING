/-
Braun–Chung–Graham 2025 (J. Scheduling 28:529–544), m = 4.

Additive lower bound (Theorem 1): for every deterministic online algorithm A
there are sequences σ_r with n = 8r + 9 jobs such that
    τ_A(σ_r) ≥ √3 · τ_o(σ_r) − (2 − √3),
hence no asymptotic competitive ratio below √3.

Construction (Sections 2–3, asymptotic version):
  α = 1 + √3 (root of 2α³ − 5α² − 2α + 2 = 0), q = 2α²
  L_k = q^k          (L-layer: four identical jobs)
  S_k = α·q^k        (S-layer: four jobs for k = 0, else three jobs + one plus job)
  S⁺_k = S_k + 2S_{k−1} = q^k·(α + 1/α)   (plus job, k ≥ 1)
  F = 2S_r           (final job)
Sequence order (Table 3): L₀×4, S₀×4, then for k = 1..r: L_k×4, S_k×3, S⁺_k; finally F.

Numerically verified (exact Q(√3) arithmetic, r ≤ 4, exhaustive OPT enumeration):
  OPT(σ_r) = F = 2S_r, the forced makespan equals √3·F − (2−√3) exactly, and
  OPT after the prefix ending at S⁺_k equals S⁺_k + L_k.
Remaining (future work): the forcing induction (Table 3 is the only escape-free
schedule), the OPT packing (Table 7), and the main theorem.
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

noncomputable section

/-! ### Parameters -/

/-- α = 1 + √3, the root driving the construction. -/
def braunα : ℝ := 1 + Real.sqrt 3

/-- Geometric ratio between consecutive layers, q = 2α². -/
def braunQ : ℝ := 2 * braunα ^ 2

lemma braunα_pos : 0 < braunα := by
  dsimp [braunα]
  linarith [Real.sqrt_nonneg 3]

lemma braunα_gt_two : 2 < braunα := by
  dsimp [braunα]
  have h : Real.sqrt 1 < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_one] at h
  linarith

/-- α² − 2α − 2 = 0, the minimal polynomial of 1 + √3. -/
lemma braun_poly2 : braunα ^ 2 - 2 * braunα - 2 = 0 := by
  dsimp [braunα]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [hs]

/-- The polynomial identity 2α³ − 5α² − 2α + 2 = 0 used in the ratio computation. -/
lemma braun_poly : 2 * braunα ^ 3 - 5 * braunα ^ 2 - 2 * braunα + 2 = 0 := by
  have h : 2 * braunα ^ 3 - 5 * braunα ^ 2 - 2 * braunα + 2 =
      (2 * braunα - 1) * (braunα ^ 2 - 2 * braunα - 2) := by
    ring
  rw [h, braun_poly2]
  ring

lemma braunQ_gt_one : 1 < braunQ := by
  dsimp [braunQ]
  have h : 2 < braunα := braunα_gt_two
  have h4 : 4 < braunα ^ 2 := by nlinarith
  nlinarith

lemma braunQ_ne_one : braunQ ≠ 1 := by
  intro h; exact lt_irrefl _ (h ▸ braunQ_gt_one)

lemma braunQ_sub_one_ne_zero : braunQ - 1 ≠ 0 := by
  intro h; exact braunQ_ne_one (by linarith)

lemma braunQ_pos : 0 < braunQ := by linarith [braunQ_gt_one]

/-! ### Layer sizes -/

/-- L_k = q^k: the four identical jobs of the k-th L-layer. -/
def braunL (k : ℕ) : ℝ := braunQ ^ k

/-- S_k = α·L_k: the regular jobs of the k-th S-layer. -/
def braunS (k : ℕ) : ℝ := braunα * braunL k

/-- S⁺_k = S_k + 2S_{k−1}: the plus job of the k-th S-layer (k ≥ 1). -/
def braunSp (k : ℕ) : ℝ := braunS k + 2 * braunS (k - 1)

/-- F = 2S_r: the final job of the r-th construction. -/
def braunF (r : ℕ) : ℝ := 2 * braunS r

lemma braunL_pos (k : ℕ) : 0 < braunL k := by
  exact pow_pos braunQ_pos k

lemma braunS_pos (k : ℕ) : 0 < braunS k := by
  exact mul_pos braunα_pos (braunL_pos k)

lemma braunSp_pos (k : ℕ) : 0 < braunSp k := by
  dsimp [braunSp]
  exact add_pos (mul_pos braunα_pos (braunL_pos k))
    (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos braunα_pos (braunL_pos (k - 1))))

lemma braunF_pos (r : ℕ) : 0 < braunF r := by
  dsimp [braunF]
  exact mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos braunα_pos (braunL_pos r))

/-- L_k = 2α·S_{k−1} (k ≥ 1), the recurrence of the paper. -/
lemma braunL_eq_two_α_S_pred (k : ℕ) (hk : 1 ≤ k) :
    braunL k = 2 * braunα * braunS (k - 1) := by
  dsimp [braunL, braunS]
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk', pow_succ']
  dsimp [braunQ]
  ring

/-- Closed form of the plus job: S⁺_k = L_k·(α + 1/α) (k ≥ 1). -/
lemma braunSp_closed (k : ℕ) (hk : 1 ≤ k) :
    braunSp k = braunL k * (braunα + 1 / braunα) := by
  dsimp [braunSp, braunS, braunL]
  have hα : braunα ≠ 0 := by linarith [braunα_pos]
  have hk' : (k - 1) + 1 = k := by omega
  have hpred : braunQ ^ (k - 1) = braunQ ^ k / braunQ := by
    calc braunQ ^ (k - 1)
        = braunQ ^ (k - 1) * braunQ / braunQ := by field_simp [braunQ_pos.ne']
    _ = braunQ ^ ((k - 1) + 1) / braunQ := by rw [pow_succ']; ring
    _ = braunQ ^ k / braunQ := by rw [hk']
  rw [hpred]
  dsimp [braunQ]
  field_simp [hα]

/-! ### Algebraic identities behind the √3 ratio -/

/-- (√3 − 1) = α − 2, a convenient rewriting form. -/
lemma braun_sqrt3_sub_one : Real.sqrt 3 - 1 = braunα - 2 := by
  dsimp [braunα]; ring

/-- (2 − √3) = 3 − α, a convenient rewriting form. -/
lemma braun_two_sub_sqrt3 : 2 - Real.sqrt 3 = 3 - braunα := by
  dsimp [braunα]; ring

/-- (1 + α)·q = 2α(√3 − 1)(q − 1): makes the geometric-sum coefficient collapse. -/
lemma braun_sum_coeff :
    (1 + braunα) * braunQ = 2 * braunα * (Real.sqrt 3 - 1) * (braunQ - 1) := by
  rw [braun_sqrt3_sub_one]
  have hp : 2 * braunα * (braunα - 2) * (braunQ - 1) - (1 + braunα) * braunQ =
      2 * braunα * (2 * braunα ^ 3 - 5 * braunα ^ 2 - 2 * braunα + 2) := by
    dsimp [braunQ]
    ring
  rw [braun_poly] at hp
  ring_nf at hp
  linarith

/-- 2α(√3 − 1)/q = 2 − √3: the additive constant. -/
lemma braun_additive_coeff :
    2 * braunα * (Real.sqrt 3 - 1) / braunQ = 2 - Real.sqrt 3 := by
  rw [div_eq_iff braunQ_pos.ne']
  rw [braun_sqrt3_sub_one, braun_two_sub_sqrt3]
  dsimp [braunQ]
  have hp : (3 - braunα) * (2 * braunα ^ 2) - 2 * braunα * (braunα - 2) =
      -2 * braunα * (braunα ^ 2 - 2 * braunα - 2) := by
    ring
  rw [braun_poly2] at hp
  ring_nf at hp
  linarith

/-- The limiting ratio identity: 1 + α(1+α)/(q−1) = √3. -/
lemma braun_ratio_identity :
    1 + braunα * (1 + braunα) / (braunQ - 1) = Real.sqrt 3 := by
  have hy : braunQ - 1 ≠ 0 := braunQ_sub_one_ne_zero
  have h : (braunQ - 1) + braunα * (1 + braunα) = Real.sqrt 3 * (braunQ - 1) := by
    have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
    rw [hs3]
    dsimp [braunQ]
    have hp : (2 * braunα ^ 2 - 1) + braunα * (1 + braunα) -
        (braunα - 1) * (2 * braunα ^ 2 - 1) =
        -(2 * braunα ^ 3 - 5 * braunα ^ 2 - 2 * braunα + 2) := by
      ring
    linarith [hp, braun_poly]
  have h' : 1 + braunα * (1 + braunα) / (braunQ - 1) =
      ((braunQ - 1) + braunα * (1 + braunα)) / (braunQ - 1) := by
    field_simp [hy]
  rw [h', h]
  field_simp [hy]

/-! ### Layer sums (closed forms) -/

/-- Cumulative L-layer sum Σ_{k≤r} L_k. -/
def braunSumL (r : ℕ) : ℝ := ∑ k ∈ Finset.range (r + 1), braunL k

/-- Cumulative Σ_{k≤r} (L_k + S_k) = (1 + α)·Σ_{k≤r} L_k. -/
def braunSumLS (r : ℕ) : ℝ := ∑ k ∈ Finset.range (r + 1), (braunL k + braunS k)

lemma braunSumLS_eq (r : ℕ) : braunSumLS r = (1 + braunα) * braunSumL r := by
  dsimp [braunSumLS, braunSumL, braunS]
  rw [Finset.sum_add_distrib]
  rw [show (∑ k ∈ Finset.range (r + 1), braunα * braunL k) =
      braunα * ∑ k ∈ Finset.range (r + 1), braunL k by rw [Finset.mul_sum]]
  ring

/-- Geometric sum: Σ_{k≤r} q^k = (q^{r+1} − 1)/(q − 1). -/
lemma braun_geom_sum (r : ℕ) :
    braunSumL r = (braunQ ^ (r + 1) - 1) / (braunQ - 1) := by
  dsimp [braunSumL, braunL]
  induction r with
  | zero =>
      field_simp [braunQ_sub_one_ne_zero]
      simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [braunQ_sub_one_ne_zero]
      ring

/-! ### The adversary sequence (Table 3 order) -/

/-- One S-layer block for k ≥ 1: L_k×4, S_k×3, S⁺_k. -/
def braunLayerBlock (k : ℕ) : List ℝ :=
  List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k) ++ [braunSp k]

lemma braunLayerBlock_length (k : ℕ) : (braunLayerBlock k).length = 8 := by
  dsimp [braunLayerBlock]

/-- Concatenation of the blocks 1..r. -/
def braunBlocks : ℕ → List ℝ
  | 0 => []
  | r + 1 => braunBlocks r ++ braunLayerBlock (r + 1)

lemma braunBlocks_length (r : ℕ) : (braunBlocks r).length = 8 * r := by
  induction r with
  | zero => dsimp [braunBlocks]
  | succ r ih =>
      dsimp [braunBlocks]
      rw [List.length_append, ih, braunLayerBlock_length]
      omega

/-- The full sequence σ_r: L₀×4, S₀×4, blocks k = 1..r, final job F. -/
def braunSeq (r : ℕ) : JobSequence :=
  List.replicate 4 (braunL 0) ++ List.replicate 4 (braunS 0) ++
  braunBlocks r ++ [braunF r]

lemma braunSeq_length (r : ℕ) : (braunSeq r).length = 8 * r + 9 := by
  dsimp [braunSeq]
  simp [braunBlocks_length]

/-! ### Forced schedule makespan (Table 3) and the additive identity -/

/-- Makespan of the forced Table-3 schedule: P1 collects all L_k, S_k and F. -/
def braunForcedMakespan (r : ℕ) : ℝ := braunSumLS r + braunF r

lemma braunForcedMakespan_closed (r : ℕ) :
    braunForcedMakespan r =
      (1 + braunα) * (braunQ ^ (r + 1) - 1) / (braunQ - 1) + braunF r := by
  dsimp [braunForcedMakespan]
  rw [braunSumLS_eq, braun_geom_sum]
  field_simp [braunQ_sub_one_ne_zero]

/-- The additive identity (exact for every r):
    forced makespan = √3 · F − (2 − √3). -/
theorem braun_additive_identity (r : ℕ) :
    braunForcedMakespan r = Real.sqrt 3 * braunF r - (2 - Real.sqrt 3) := by
  rw [braunForcedMakespan_closed]
  have hcoeff : (1 + braunα) / (braunQ - 1) =
      2 * braunα * (Real.sqrt 3 - 1) / braunQ := by
    have hq : braunQ - 1 ≠ 0 := braunQ_sub_one_ne_zero
    field_simp [hq, braunQ_pos.ne']
    nlinarith [braun_sum_coeff]
  have hmul : (2 - Real.sqrt 3) * braunQ = 2 * braunα * (Real.sqrt 3 - 1) := by
    have := congrArg (· * braunQ) braun_additive_coeff
    field_simp [braunQ_pos.ne'] at this
    linarith
  calc
    (1 + braunα) * (braunQ ^ (r + 1) - 1) / (braunQ - 1) + braunF r
      = (1 + braunα) / (braunQ - 1) * (braunQ ^ (r + 1) - 1) + braunF r := by ring
    _ = 2 * braunα * (Real.sqrt 3 - 1) / braunQ * (braunQ ^ (r + 1) - 1) + braunF r := by
        rw [hcoeff]
    _ = (2 - Real.sqrt 3) * (braunQ ^ (r + 1) - 1) + braunF r := by
        rw [braun_additive_coeff]
    _ = (2 - Real.sqrt 3) * braunQ ^ (r + 1) - (2 - Real.sqrt 3) + braunF r := by ring
    _ = Real.sqrt 3 * braunF r - (2 - Real.sqrt 3) := by
        dsimp [braunF, braunS, braunL]
        have hqr : braunQ ^ (r + 1) = braunQ * braunQ ^ r := by rw [pow_succ']
        rw [hqr]
        have hstep : (2 - Real.sqrt 3) * (braunQ * braunQ ^ r) =
            (2 - Real.sqrt 3) * braunQ * braunQ ^ r := by ring
        rw [hstep, hmul]
        ring_nf

/-- F is a job of σ_r, hence OPT(σ_r) ≥ F (largest-job lower bound). -/
theorem braun_opt_ge_F (r : ℕ) : braunF r ≤ OPT (braunSeq r) := by
  apply le_trans _ (opt_ge_max_job (braunSeq r))
  exact maxJobSize_ge_each (braunSeq r) (braunF r) (by
    dsimp [braunSeq]
    simp)

end
