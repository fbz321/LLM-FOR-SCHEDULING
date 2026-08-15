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
All OPT statements use the sound v2 foundation `optMakespan` (Basic.lean); the old
opaque OPT axioms are inconsistent and must not be used (see findings 2026-08-08).

Formalized (0 sorry):
  - Table 6: OPT of the prefix through S⁺_k equals S⁺_k + L_k (`braun_opt_prefix_Sp`),
    with the block-forcing counting argument `braunLayerBlock_makespan_ge`.
  - Theorem 1: `braun_asymptotic_lower_bound` — for every deterministic online
    algorithm on 4 machines there is a sequence with makespan ≥ √3·OPT − (2−√3).
    The adaptive adversary (r = 1 instance, 17 jobs) releases L₀×4, S₀×4, then
    the block {L₁×4, S₁×3, S⁺₁}, and finally F: any deviation at L₀/S₀/L₁/S₁
    triggers a trap (ratios 2, √3, (Φ₀+2L₁)/(Φ₀+L₁), (Φ₀+L₁+2S₁)/(S₁+L₁)), the
    S⁺₁ trap is exact by `braun_prefix_additive_identity`, and a clean schedule
    is finished off by F with `braun_additive_identity` + `braun_opt_eq_F`.
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

/-- Cumulative Σ_{k≤r} S_k. -/
def braunSumS (r : ℕ) : ℝ := ∑ k ∈ Finset.range (r + 1), braunS k

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

/-- Geometric sum variant: Σ_{k<r} q^k = (q^r − 1)/(q − 1). -/
lemma braun_geom_sum_lt (r : ℕ) :
    (∑ k ∈ Finset.range r, braunQ ^ k) = (braunQ ^ r - 1) / (braunQ - 1) := by
  induction r with
  | zero =>
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

/-! ### Table-7 explicit assignment

Machines: 0 = M0 (final job F), 1 = M1 (S⁺_k + 2L_k per layer + 2S₀),
2 = M2 (two top S_r), 3 = M3 (everything else).
Within one layer block (positions 0..7: L,L,L,L,S,S,S,S⁺):
  pos 0,1 (first two L) → M1;  pos 2,3 (last two L) → M3;
  pos 4,5 (first two S) → M2 if top layer else M3;  pos 6 (last S) → M3;
  pos 7 (S⁺) → M1. -/

/-- Assignment of the jobs inside one layer block. -/
def braunBlockAssign (r k : ℕ) : Fin (braunLayerBlock k).length → Fin 4 :=
  fun i =>
    if i.1 < 2 then 1
    else if i.1 < 4 then 3
    else if i.1 < 7 then (if k = r ∧ i.1 < 6 then 2 else 3)
    else 1

/-- Loads induced on the four machines by one layer block:
    M1 gets 2L_k + S⁺_k, M2 gets 2S_k (top layer only), M3 gets the rest. -/
lemma braunBlockAssign_loads (r k : ℕ) :
    scheduleLoads (m := 4) (braunLayerBlock k) (braunBlockAssign r k) 0 = 0 ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunBlockAssign r k) 1 = 2 * braunL k + braunSp k ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunBlockAssign r k) 2 =
      (if k = r then 2 * braunS k else 0) ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunBlockAssign r k) 3 =
      (if k = r then 2 * braunL k + braunS k else 2 * braunL k + 3 * braunS k) := by
  -- 展开 block 为具体列表，逐位置计算
  unfold braunLayerBlock braunBlockAssign
  by_cases hkr : k = r
  · simp [scheduleLoads, hkr, Fin.sum_univ_succ]
    repeat (constructor <;> try ring) <;> trivial
  · simp [scheduleLoads, hkr, Fin.sum_univ_succ]
    repeat (constructor <;> try ring) <;> trivial

/-- Assignment of the initial L₀ jobs: all four go to M3. -/
def braunL0Assign : Fin (List.replicate 4 (braunL 0)).length → Fin 4 := fun _ => 3

/-- Assignment of the initial S₀ jobs: first two to M1, last two to M3. -/
def braunS0Assign : Fin (List.replicate 4 (braunS 0)).length → Fin 4 :=
  fun i => if i.1 < 2 then 1 else 3

/-- Assignment of the final job F: goes to M0. -/
def braunFAssign (r : ℕ) : Fin [braunF r].length → Fin 4 := fun _ => 0

/-- Loads of the initial S₀ jobs: M1 gets 2S₀, M3 gets 2S₀. -/
lemma braunS0Assign_loads :
    scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 1 = 2 * braunS 0 ∧
    scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 3 = 2 * braunS 0 := by
  unfold braunS0Assign
  simp [scheduleLoads, Fin.sum_univ_succ]
  all_goals ring

/-- Loads of the initial L₀ jobs: all four on M3. -/
lemma braunL0Assign_loads :
    scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 3 = 4 * braunL 0 := by
  unfold braunL0Assign
  simp [scheduleLoads, Fin.sum_univ_succ]
  ring

/-- Loads of the final job F: all on M0. -/
lemma braunFAssign_loads (r : ℕ) :
    scheduleLoads (m := 4) [braunF r] (braunFAssign r) 0 = braunF r := by
  unfold braunFAssign
  simp [scheduleLoads, Fin.sum_univ_succ]

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

/-- Recursive assignment of the blocks 1..r (each block via `braunBlockAssign`),
    built with `appendAssign` so that `scheduleLoads_append` applies. -/
noncomputable def braunBlocksAssign (r k : ℕ) : Fin (braunBlocks r).length → Fin 4 :=
  match r with
  | 0 => fun i => (False.elim (by
      have hlen : (braunBlocks 0).length = 0 := braunBlocks_length 0
      have : i.1 < 0 := by simpa [hlen] using i.2
      omega))
  | r + 1 =>
      appendAssign (m := 4) (braunBlocks r) (braunLayerBlock (r + 1))
        (braunBlocksAssign r k) (braunBlockAssign k (r + 1))

/-- Loads of the blocks 1..r: sums of the per-block loads. -/
lemma braunBlocksAssign_loads (r k : ℕ) (j : Fin 4) :
    scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r k) j =
      ∑ t ∈ Finset.range r, scheduleLoads (m := 4) (braunLayerBlock (t + 1)) (braunBlockAssign k (t + 1)) j := by
  induction r with
  | zero =>
      unfold braunBlocksAssign
      simp [scheduleLoads, braunBlocks]
      exact Finset.sum_empty
  | succ r ih =>
      unfold braunBlocksAssign
      change scheduleLoads (m := 4) (braunBlocks r ++ braunLayerBlock (r + 1))
        (appendAssign (m := 4) (braunBlocks r) (braunLayerBlock (r + 1))
          (braunBlocksAssign r k) (braunBlockAssign k (r + 1))) j =
        ∑ t ∈ Finset.range (r + 1), scheduleLoads (m := 4) (braunLayerBlock (t + 1)) (braunBlockAssign k (t + 1)) j
      rw [scheduleLoads_append]
      rw [ih]
      rw [Finset.sum_range_succ]

/-- The full sequence σ_r: L₀×4, S₀×4, blocks k = 1..r, final job F. -/
def braunSeq (r : ℕ) : JobSequence :=
  List.replicate 4 (braunL 0) ++ List.replicate 4 (braunS 0) ++
  braunBlocks r ++ [braunF r]

lemma braunSeq_length (r : ℕ) : (braunSeq r).length = 8 * r + 9 := by
  dsimp [braunSeq]
  simp [braunBlocks_length]

/-- The full Table-7 assignment of σ_r to four machines.
    Domain is directly `Fin (braunSeq r).length`; the inner `appendAssign`
    targets the right-associative `++` decomposition of `braunSeq`. -/
noncomputable def braunAssign (r : ℕ) : Fin (braunSeq r).length → Fin 4 :=
  fun i =>
    appendAssign (m := 4) (List.replicate 4 (braunL 0))
      (List.replicate 4 (braunS 0) ++ (braunBlocks r ++ [braunF r]))
      braunL0Assign
      (appendAssign (m := 4) (List.replicate 4 (braunS 0))
        (braunBlocks r ++ [braunF r])
        braunS0Assign
        (appendAssign (m := 4) (braunBlocks r) [braunF r]
          (braunBlocksAssign r r) (braunFAssign r)))
      ⟨i.1, by
        change i.1 < (List.replicate 4 (braunL 0) ++
          (List.replicate 4 (braunS 0) ++ (braunBlocks r ++ [braunF r]))).length
        exact i.2⟩

/-- σ_r's type-coerced form matches the `braunAssign` domain. -/
lemma braunSeq_eq_decomp (r : ℕ) :
    braunSeq r = List.replicate 4 (braunL 0) ++
      (List.replicate 4 (braunS 0) ++ (braunBlocks r ++ [braunF r])) := by
  rfl

/-- The load on machine `j` under the full assignment decomposes as
    L₀-part + S₀-part + blocks-part + F-part. -/
lemma braunAssign_loads_decomp (r : ℕ) (j : Fin 4) :
    scheduleLoads (m := 4) (braunSeq r) (braunAssign r) j =
      scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign j +
      scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign j +
      scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r r) j +
      scheduleLoads (m := 4) [braunF r] (braunFAssign r) j := by
  -- 组装（机械）：先归约 braunSeq 与 braunAssign 的展开，再逐层 scheduleLoads_append
  unfold braunAssign
  change scheduleLoads (m := 4) (List.replicate 4 (braunL 0) ++
      (List.replicate 4 (braunS 0) ++ (braunBlocks r ++ [braunF r])))
      (appendAssign (m := 4) (List.replicate 4 (braunL 0))
        (List.replicate 4 (braunS 0) ++ (braunBlocks r ++ [braunF r]))
        braunL0Assign
        (appendAssign (m := 4) (List.replicate 4 (braunS 0))
          (braunBlocks r ++ [braunF r])
          braunS0Assign
          (appendAssign (m := 4) (braunBlocks r) [braunF r]
            (braunBlocksAssign r r) (braunFAssign r)))) j =
      scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign j +
      scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign j +
      scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r r) j +
      scheduleLoads (m := 4) [braunF r] (braunFAssign r) j
  rw [scheduleLoads_append]
  rw [scheduleLoads_append]
  rw [scheduleLoads_append]
  ring

/- OPT of σ_r is at most F (Table-7 packing upper bound) — stated and proved at
   the end of the file, after the machine-load lemmas it depends on. -/

/-- All jobs of σ_r are positive. -/
lemma braunSeq_pos (r : ℕ) : ∀ p ∈ braunSeq r, 0 < p := by
  have hb : ∀ q ∈ braunBlocks r, 0 < q := by
    intro q hq
    induction r generalizing q with
    | zero => simp [braunBlocks] at hq
    | succ r ih =>
        unfold braunBlocks at hq
        rw [List.mem_append] at hq
        rcases hq with hq | hq
        · exact ih q hq
        · unfold braunLayerBlock at hq
          rw [List.mem_append] at hq
          rcases hq with hq | hq
          · rw [List.mem_append] at hq
            rcases hq with hq | hq
            · rcases List.mem_replicate.mp hq with ⟨_, heq⟩
              rw [heq]; exact braunL_pos (r + 1)
            · rcases List.mem_replicate.mp hq with ⟨_, heq⟩
              rw [heq]; exact braunS_pos (r + 1)
          · rw [List.mem_singleton] at hq; rw [hq]; exact braunSp_pos (r + 1)
  intro p hp
  unfold braunSeq at hp
  rw [List.mem_append] at hp
  rcases hp with h | h
  · rw [List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_append] at h
      rcases h with h | h
      · rcases List.mem_replicate.mp h with ⟨_, heq⟩
        rw [heq]; exact braunL_pos 0
      · rcases List.mem_replicate.mp h with ⟨_, heq⟩
        rw [heq]; exact braunS_pos 0
    · exact hb p h
  · rw [List.mem_singleton] at h; rw [h]; exact braunF_pos r
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

/-- Sum of one layer block (k ≥ 1): 4·L_k + 3·S_k + S⁺_k. -/
lemma braunLayerBlock_sum (k : ℕ) : (braunLayerBlock k).sum = 4 * braunL k + 3 * braunS k + braunSp k := by
  unfold braunLayerBlock
  simp
  ring

/-- Sum of all blocks 1..r (as a range sum over k+1):
    Σ_{k=0..r−1} (4L_{k+1} + 3S_{k+1} + S⁺_{k+1}). -/
lemma braunBlocks_sum (r : ℕ) :
    (braunBlocks r).sum = ∑ k ∈ Finset.range r, (4 * braunL (k + 1) + 3 * braunS (k + 1) + braunSp (k + 1)) := by
  induction r with
  | zero => simp [braunBlocks]
  | succ r ih =>
      unfold braunBlocks
      rw [List.sum_append, ih, braunLayerBlock_sum]
      simp [Finset.sum_range_succ]

/-- Decompose the sequence sum into layers: 4L₀ + 4S₀ + blocks + F. -/
lemma braunSeq_sum_decomp (r : ℕ) :
    (braunSeq r).sum = 4 * braunL 0 + 4 * braunS 0 + (braunBlocks r).sum + braunF r := by
  unfold braunSeq
  rw [List.sum_append, List.sum_append, List.sum_append]
  simp
  ring

/-- Total load of σ_r:
    totalLoad(σ_r) = 4·Σ_{k≤r} L_k + 6·Σ_{k≤r} S_k
    (derivation: 4 per L-layer, and S-contribution 4S₀ + Σ(3S_k+S⁺_k)
     = 4S₀ + Σ(4S_k+2S_{k−1}) = 4ΣS + 2(ΣS − S_r) = 6ΣS − F, then +F). -/
lemma braun_totalLoad_eq (r : ℕ) :
    totalLoad (braunSeq r) = 4 * braunSumL r + 6 * braunSumS r := by
  unfold totalLoad
  rw [braunSeq_sum_decomp, braunBlocks_sum]
  -- 左侧 = 4L₀ + 4S₀ + Σ_{k<r}(4L_{k+1}+3S_{k+1}+S⁺_{k+1}) + F
  -- S⁺_{k+1} = S_{k+1} + 2S_k 代入：Σ(4L + 4S + 2S_k)
  have hsp : ∑ k ∈ Finset.range r, braunSp (k + 1) =
      ∑ k ∈ Finset.range r, (braunS (k + 1) + 2 * braunS k) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [braunSp]
  have hsumS : 4 * braunS 0 + ∑ k ∈ Finset.range r, (3 * braunS (k + 1) + braunSp (k + 1)) =
      6 * braunSumS r - braunF r := by
    -- 用 calc 逐步：Sp_{k+1} = S_{k+1} + 2S_k
    calc
      4 * braunS 0 + ∑ k ∈ Finset.range r, (3 * braunS (k + 1) + braunSp (k + 1))
          = 4 * braunS 0 + ∑ k ∈ Finset.range r, (4 * braunS (k + 1) + 2 * braunS k) := by
              apply congrArg (fun t : ℝ => 4 * braunS 0 + t)
              apply Finset.sum_congr rfl
              intro k hk
              dsimp [braunSp]
              ring
      _ = 4 * braunS 0 + 4 * ∑ k ∈ Finset.range r, braunS (k + 1) + 2 * ∑ k ∈ Finset.range r, braunS k := by
              rw [Finset.sum_add_distrib]
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
              ring
      _ = 4 * braunS 0 + 4 * (braunSumS r - braunS 0) + 2 * (braunSumS r - braunS r) := by
              -- Σ_{k<r}S_{k+1} = ΣS − S₀ 与 Σ_{k<r}S_k = ΣS − S_r
              have htail : ∑ k ∈ Finset.range r, braunS (k + 1) = braunSumS r - braunS 0 := by
                have : ∑ k ∈ Finset.range r, braunS (k + 1) + braunS 0 = braunSumS r := by
                  rw [braunSumS]
                  rw [← Finset.sum_range_succ']
                linarith
              have htail2 : ∑ k ∈ Finset.range r, braunS k = braunSumS r - braunS r := by
                have : ∑ k ∈ Finset.range r, braunS k + braunS r = braunSumS r := by
                  rw [braunSumS]
                  rw [← Finset.sum_range_succ]
                linarith
              rw [htail, htail2]
      _ = 6 * braunSumS r - braunF r := by
              dsimp [braunF]
              ring
  -- L 部分
  have hsumL : 4 * braunL 0 + ∑ k ∈ Finset.range r, 4 * braunL (k + 1) = 4 * braunSumL r := by
    have : ∑ k ∈ Finset.range r, braunL (k + 1) + braunL 0 = braunSumL r := by
      rw [braunSumL]
      rw [← Finset.sum_range_succ']
    rw [← Finset.mul_sum]
    nlinarith
  -- 总装配：4L₀ + 4S₀ + Σ(4L+3S+S⁺) + F = 4ΣL + 6ΣS
  calc
    4 * braunL 0 + 4 * braunS 0 + (∑ k ∈ Finset.range r, (4 * braunL (k + 1) + 3 * braunS (k + 1) + braunSp (k + 1))) + braunF r
        = (4 * braunL 0 + ∑ k ∈ Finset.range r, 4 * braunL (k + 1)) +
          (4 * braunS 0 + ∑ k ∈ Finset.range r, (3 * braunS (k + 1) + braunSp (k + 1))) + braunF r := by
            simp_rw [Finset.sum_add_distrib]
            abel
    _ = 4 * braunSumL r + (6 * braunSumS r - braunF r) + braunF r := by
            rw [hsumL, hsumS]
    _ = 4 * braunSumL r + 6 * braunSumS r := by ring

/-- Key packing invariant: total work of σ_r = 4·F − (4+6α)/(q−1),
    a constant deficit independent of r. This is the algebraic heart of the
    Table-7 packing: four machines of capacity F have total capacity 4F,
    only (4+6α)/(q−1) ≈ 1.46 above the total work, so a packing into
    four bins of size F exists only if it is nearly tight. -/
theorem braun_total_work (r : ℕ) :
    totalLoad (braunSeq r) = 4 * braunF r - (4 + 6 * braunα) / (braunQ - 1) := by
  rw [braun_totalLoad_eq]
  have hq : braunQ - 1 ≠ 0 := braunQ_sub_one_ne_zero
  have hqpos : 0 < braunQ := by dsimp [braunQ]; nlinarith [braunα_pos]
  have hqr : braunQ ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hqpos)
  -- 核心系数坍缩：(4+6α)·q = 8α·(q−1)，由 α²−2α−2=0 保证
  have hcoef : (4 + 6 * braunα) * braunQ = 8 * braunα * (braunQ - 1) := by
    dsimp [braunQ]
    have hp : (4 + 6 * braunα) * (2 * braunα ^ 2) - 8 * braunα * (2 * braunα ^ 2 - 1) =
        -4 * braunα * (braunα ^ 2 - 2 * braunα - 2) := by
      ring
    rw [braun_poly2] at hp
    nlinarith
  -- 几何和项化简：(4+6α)·(q^{r+1}−1)/(q−1) = 8α·q^r − (4+6α)/(q−1)
  have hgeom : (4 + 6 * braunα) * (braunQ ^ (r + 1) - 1) / (braunQ - 1) =
      8 * braunα * braunQ ^ r - (4 + 6 * braunα) / (braunQ - 1) := by
    have hsucc : braunQ ^ (r + 1) = braunQ * braunQ ^ r := by
      rw [pow_succ']
    calc
      (4 + 6 * braunα) * (braunQ ^ (r + 1) - 1) / (braunQ - 1)
          = ((4 + 6 * braunα) * (braunQ * braunQ ^ r) - (4 + 6 * braunα)) / (braunQ - 1) := by
              rw [hsucc]
              ring
      _ = (8 * braunα * (braunQ - 1) * braunQ ^ r - (4 + 6 * braunα)) / (braunQ - 1) := by
              rw [← hcoef]
              ring
      _ = 8 * braunα * braunQ ^ r - (4 + 6 * braunα) / (braunQ - 1) := by
              field_simp [hq]
  calc
    4 * braunSumL r + 6 * braunSumS r
        = (4 + 6 * braunα) * braunSumL r := by
            dsimp [braunSumS, braunS]
            have h6 : 6 * (∑ k ∈ Finset.range (r + 1), braunα * braunL k) =
                6 * braunα * (∑ k ∈ Finset.range (r + 1), braunL k) := by
              calc
                6 * (∑ k ∈ Finset.range (r + 1), braunα * braunL k)
                    = ∑ k ∈ Finset.range (r + 1), (6 * (braunα * braunL k)) := by
                        rw [Finset.mul_sum]
                _ = ∑ k ∈ Finset.range (r + 1), ((6 * braunα) * braunL k) := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        ring
                _ = 6 * braunα * (∑ k ∈ Finset.range (r + 1), braunL k) := by
                        rw [← Finset.mul_sum]
            rw [h6]
            dsimp [braunSumL]
            ring
    _ = (4 + 6 * braunα) * (braunQ ^ (r + 1) - 1) / (braunQ - 1) := by
            rw [braun_geom_sum]
            ring
    _ = 8 * braunα * braunQ ^ r - (4 + 6 * braunα) / (braunQ - 1) := hgeom
    _ = 4 * braunF r - (4 + 6 * braunα) / (braunQ - 1) := by
            dsimp [braunF, braunS, braunL]
            ring

/-- M1 machine load in the Table-7 packing:
    Σ_{k=1..r}(S⁺_k + 2·L_k) + 2·S₀ = F.
    Telescoping: S⁺_k + 2L_k = (α+2)·q^k + 2α·q^{k−1}, and the combined
    coefficient [(α+2)q + 2α] equals 2α(q−1) by the minimal polynomial,
    so the sum collapses to 2α·q^r = F. -/
theorem braun_M1_eq_F (r : ℕ) :
    (∑ k ∈ Finset.range r, (braunSp (k + 1) + 2 * braunL (k + 1))) + 2 * braunS 0 = braunF r := by
  -- 展开 S⁺_{k+1} = S_{k+1} + 2S_k, 按 q^{k+1} 与 q^k 分组
  have hsp : ∑ k ∈ Finset.range r, (braunSp (k + 1) + 2 * braunL (k + 1)) =
      ∑ k ∈ Finset.range r, ((braunα + 2) * braunQ ^ (k + 1) + 2 * braunα * braunQ ^ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [braunSp, braunS, braunL]
    ring
  rw [hsp]
  -- 拆成两个和: (α+2)·Σq^{k+1} + 2α·Σq^k
  have hsplit : ∑ k ∈ Finset.range r, ((braunα + 2) * braunQ ^ (k + 1) + 2 * braunα * braunQ ^ k) =
      (braunα + 2) * (∑ k ∈ Finset.range r, braunQ ^ (k + 1)) +
      2 * braunα * (∑ k ∈ Finset.range r, braunQ ^ k) := by
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsplit]
  -- Σ_{k<r}q^{k+1} = q·Σ_{k<r}q^k
  have hsum1 : ∑ k ∈ Finset.range r, braunQ ^ (k + 1) = braunQ * (∑ k ∈ Finset.range r, braunQ ^ k) := by
    calc
      ∑ k ∈ Finset.range r, braunQ ^ (k + 1)
          = ∑ k ∈ Finset.range r, (braunQ * braunQ ^ k) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [pow_succ']
      _ = braunQ * (∑ k ∈ Finset.range r, braunQ ^ k) := by
              rw [Finset.mul_sum]
  rw [hsum1]
  -- 系数坍缩: (α+2)q + 2α = 2α(q−1)
  have hcoef : (braunα + 2) * braunQ + 2 * braunα = 2 * braunα * (braunQ - 1) := by
    dsimp [braunQ]
    have hp : (braunα + 2) * (2 * braunα ^ 2) + 2 * braunα - 2 * braunα * (2 * braunα ^ 2 - 1) =
        -2 * braunα * (braunα ^ 2 - 2 * braunα - 2) := by
      ring
    rw [braun_poly2] at hp
    nlinarith
  -- Σ_{k<r}q^k = (q^r − 1)/(q−1)
  have hgeom : ∑ k ∈ Finset.range r, braunQ ^ k = (braunQ ^ r - 1) / (braunQ - 1) :=
    braun_geom_sum_lt r
  have hq : braunQ - 1 ≠ 0 := braunQ_sub_one_ne_zero
  calc
    (braunα + 2) * (braunQ * (∑ k ∈ Finset.range r, braunQ ^ k)) +
        2 * braunα * (∑ k ∈ Finset.range r, braunQ ^ k) + 2 * braunS 0
        = ((braunα + 2) * braunQ + 2 * braunα) * (∑ k ∈ Finset.range r, braunQ ^ k) + 2 * braunα := by
            dsimp [braunS, braunL]
            norm_num
            ring
    _ = (2 * braunα * (braunQ - 1)) * (∑ k ∈ Finset.range r, braunQ ^ k) + 2 * braunα := by
            rw [hcoef]
    _ = 2 * braunα * (braunQ - 1) * ((braunQ ^ r - 1) / (braunQ - 1)) + 2 * braunα := by
            rw [hgeom]
    _ = 2 * braunα * (braunQ ^ r - 1) + 2 * braunα := by
            field_simp [hq]
    _ = 2 * braunα * braunQ ^ r := by ring
    _ = braunF r := by
            dsimp [braunF, braunS, braunL]
            ring_nf

/-- M3 machine load in the Table-7 packing: the remaining jobs (everything
    except F, the M1-jobs Σ(S⁺_k+2L_k)+2S₀, and the two top S_r's) have load
    F − (4+6α)/(q−1) < F. This is the unique machine with slack. -/
theorem braun_M3_lt_F (r : ℕ) :
    totalLoad (braunSeq r) - braunF r
      - ((∑ k ∈ Finset.range r, (braunSp (k + 1) + 2 * braunL (k + 1))) + 2 * braunS 0) - 2 * braunS r
      < braunF r := by
  have htot := braun_total_work r
  have hm1 := braun_M1_eq_F r
  have hF : 2 * braunS r = braunF r := by rfl
  have hdeficit : 0 < (4 + 6 * braunα) / (braunQ - 1) := by
    have hnum : 0 < 4 + 6 * braunα := by nlinarith [braunα_pos]
    have hden : 0 < braunQ - 1 := by linarith [braunQ_gt_one]
    positivity
  -- total − F − M1 − 2S_r = (4F−c) − F − F − F = F − c < F
  have hcalc : totalLoad (braunSeq r) - braunF r
      - ((∑ k ∈ Finset.range r, (braunSp (k + 1) + 2 * braunL (k + 1))) + 2 * braunS 0) - 2 * braunS r
      = braunF r - (4 + 6 * braunα) / (braunQ - 1) := by
    rw [htot, hm1, hF]
    ring
  rw [hcalc]
  linarith

/-- F is a job of σ_r, hence OPT(σ_r) ≥ F (largest-job lower bound).
    Uses the sound v2 foundation (`optMakespan`, minimum over assignments). -/
theorem braun_opt_ge_F (r : ℕ) : braunF r ≤ optMakespan (m := 4) (braunSeq r) := by
  apply le_trans _ (optMakespan_ge_max_job (m := 4) (braunSeq r) (fun p hp =>
    le_of_lt (braunSeq_pos r p hp)))
  exact maxJobSize_ge_each (braunSeq r) (braunF r) (by
    dsimp [braunSeq]
    simp)

/-! ### Machine loads of the Table-7 assignment `braunAssign` (r ≥ 1) -/

private lemma scheduleLoads_zero_of_forall_ne (σ : List ℝ) (a : Fin σ.length → Fin 4) (j : Fin 4)
    (h : ∀ i, a i ≠ j) : scheduleLoads (m := 4) σ a j = 0 := by
  dsimp [scheduleLoads]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : a i ≠ j := h i
  simp [hne]

/-- The load on machine 3 equals total load minus the loads on 0, 1, 2. -/
private lemma fin4_sum_extract3 (f : Fin 4 → ℝ) :
    f 3 = (∑ j : Fin 4, f j) - f 0 - f 1 - f 2 := by
  rw [Fin.sum_univ_four]
  ring

/-- Machine 0 receives exactly the final job: load = F. -/
lemma braun_load_M0_eq_F (r : ℕ) :
    scheduleLoads (m := 4) (braunSeq r) (braunAssign r) 0 = braunF r := by
  rw [braunAssign_loads_decomp r 0]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunS0Assign
    fin_cases i <;> decide
  have hblocks : scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r r) 0 = 0 := by
    rw [braunBlocksAssign_loads r r 0]
    apply Finset.sum_eq_zero
    intro t ht
    rcases braunBlockAssign_loads r (t + 1) with ⟨hb0, hb1, hb2, hb3⟩
    exact hb0
  have hF := braunFAssign_loads r
  rw [hL0, hS0, hblocks, hF]
  ring

/-- Machine 1 receives Σ(S⁺_k + 2L_k) + 2S₀ = F. -/
lemma braun_load_M1_eq_F (r : ℕ) :
    scheduleLoads (m := 4) (braunSeq r) (braunAssign r) 1 = braunF r := by
  rw [braunAssign_loads_decomp r 1]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 1 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 1 = 2 * braunS 0 :=
    braunS0Assign_loads.1
  have hblocks : scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r r) 1 =
      ∑ t ∈ Finset.range r, (2 * braunL (t + 1) + braunSp (t + 1)) := by
    rw [braunBlocksAssign_loads r r 1]
    apply Finset.sum_congr rfl
    intro t ht
    rcases braunBlockAssign_loads r (t + 1) with ⟨hb0, hb1, hb2, hb3⟩
    exact hb1
  have hF : scheduleLoads (m := 4) [braunF r] (braunFAssign r) 1 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunFAssign
    decide
  rw [hL0, hS0, hblocks, hF]
  have hcomm : (∑ t ∈ Finset.range r, (2 * braunL (t + 1) + braunSp (t + 1))) =
      ∑ t ∈ Finset.range r, (braunSp (t + 1) + 2 * braunL (t + 1)) := by
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hcomm]
  nlinarith [braun_M1_eq_F r]

/-- Machine 2 receives the two top S_r's = F (r ≥ 1).
    The block sum over `t ∈ range r` collapses because only `t + 1 = r` is
    nonzero: `braunBlockAssign` sends the first two S of the top block to M2. -/
lemma braun_load_M2_eq_F (r : ℕ) (hr : 1 ≤ r) :
    scheduleLoads (m := 4) (braunSeq r) (braunAssign r) 2 = braunF r := by
  rw [braunAssign_loads_decomp r 2]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunS0Assign
    fin_cases i <;> decide
  have hblocks : scheduleLoads (m := 4) (braunBlocks r) (braunBlocksAssign r r) 2 =
      ∑ t ∈ Finset.range r, (if t + 1 = r then 2 * braunS (t + 1) else 0) := by
    rw [braunBlocksAssign_loads r r 2]
    apply Finset.sum_congr rfl
    intro t ht
    rcases braunBlockAssign_loads r (t + 1) with ⟨hb0, hb1, hb2, hb3⟩
    exact hb2
  have hF : scheduleLoads (m := 4) [braunF r] (braunFAssign r) 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunFAssign
    decide
  rw [hL0, hS0, hblocks, hF]
  dsimp [braunF]
  have hsum_single : (∑ t ∈ Finset.range r, (if t + 1 = r then 2 * braunS (t + 1) else 0)) =
      2 * braunS r := by
    refine Eq.trans (Finset.sum_eq_single_of_mem (r - 1) ?hmem ?h₀) ?hmain
    · exact Finset.mem_range.mpr (Nat.sub_lt (Nat.succ_le_iff.mp hr) (by norm_num : 0 < 1))
    · intro b hb hne
      have hb1 : b + 1 ≠ r := by
        intro h
        have hbeq : b = r - 1 := by
          rw [← h]
          exact (Nat.add_sub_cancel b 1).symm
        exact hne hbeq
      simp [hb1]
    · have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
      rw [hpred]
      simp
  rw [hsum_single]
  ring

/-- Machine 3 receives the remainder, with load F − (4+6α)/(q−1) < F (r ≥ 1). -/
lemma braun_load_M3_lt_F (r : ℕ) (hr : 1 ≤ r) :
    scheduleLoads (m := 4) (braunSeq r) (braunAssign r) 3 < braunF r := by
  have hsum := sum_scheduleLoads (m := 4) (braunSeq r) (braunAssign r)
  have h3 := fin4_sum_extract3 (fun j => scheduleLoads (m := 4) (braunSeq r) (braunAssign r) j)
  rw [h3]
  rw [hsum]
  rw [braun_load_M0_eq_F r, braun_load_M1_eq_F r, braun_load_M2_eq_F r hr]
  rw [braun_total_work r]
  have hc : 0 < (4 + 6 * braunα) / (braunQ - 1) := by
    have hnum : 0 < 4 + 6 * braunα := by nlinarith [braunα_pos]
    have hden : 0 < braunQ - 1 := by linarith [braunQ_gt_one]
    positivity
  nlinarith

/-! ### The r = 0 base packing (no top S-layer block) -/

/-- S₀ assignment for r = 0: two to M1, two to M2. -/
noncomputable def braunS0Assign0 : Fin (List.replicate 4 (braunS 0)).length → Fin 4 :=
  fun i => if i.1 < 2 then 1 else 2

lemma braunS0Assign0_loads :
    scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 1 = 2 * braunS 0 ∧
    scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 2 = 2 * braunS 0 := by
  unfold braunS0Assign0
  simp [scheduleLoads, Fin.sum_univ_succ]
  all_goals ring

/-- Full assignment for σ₀ = L₀×4, S₀×4, F: L₀ → M3, S₀ → M1/M2, F → M0. -/
noncomputable def braunAssign0 : Fin (braunSeq 0).length → Fin 4 :=
  fun i =>
    appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0) ++ [braunF 0])
      braunL0Assign
      (appendAssign (m := 4) (List.replicate 4 (braunS 0)) [braunF 0] braunS0Assign0 (braunFAssign 0))
      ⟨i.1, by
        change i.1 < (List.replicate 4 (braunL 0) ++ (List.replicate 4 (braunS 0) ++ [braunF 0])).length
        exact i.2⟩

lemma braunAssign0_loads_decomp (j : Fin 4) :
    scheduleLoads (m := 4) (braunSeq 0) braunAssign0 j =
      scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign j +
      scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 j +
      scheduleLoads (m := 4) [braunF 0] (braunFAssign 0) j := by
  unfold braunAssign0
  change scheduleLoads (m := 4) (List.replicate 4 (braunL 0) ++ (List.replicate 4 (braunS 0) ++ [braunF 0]))
    (appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0) ++ [braunF 0])
      braunL0Assign (appendAssign (m := 4) (List.replicate 4 (braunS 0)) [braunF 0] braunS0Assign0 (braunFAssign 0))) j =
      scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign j +
      scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 j +
      scheduleLoads (m := 4) [braunF 0] (braunFAssign 0) j
  rw [scheduleLoads_append]
  rw [scheduleLoads_append]
  ring

lemma braunAssign0_load_M0 :
    scheduleLoads (m := 4) (braunSeq 0) braunAssign0 0 = braunF 0 := by
  rw [braunAssign0_loads_decomp 0]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunS0Assign0
    fin_cases i <;> decide
  have hF := braunFAssign_loads 0
  rw [hL0, hS0, hF]
  ring

lemma braunAssign0_load_M1 :
    scheduleLoads (m := 4) (braunSeq 0) braunAssign0 1 = braunF 0 := by
  rw [braunAssign0_loads_decomp 1]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 1 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 := braunS0Assign0_loads.1
  have hF : scheduleLoads (m := 4) [braunF 0] (braunFAssign 0) 1 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunFAssign
    decide
  rw [hL0, hS0, hF]
  dsimp [braunF]
  ring

lemma braunAssign0_load_M2 :
    scheduleLoads (m := 4) (braunSeq 0) braunAssign0 2 = braunF 0 := by
  rw [braunAssign0_loads_decomp 2]
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunL0Assign
    decide
  have hS0 := braunS0Assign0_loads.2
  have hF : scheduleLoads (m := 4) [braunF 0] (braunFAssign 0) 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunFAssign
    decide
  rw [hL0, hS0, hF]
  dsimp [braunF]
  ring

lemma braunAssign0_load_M3_le :
    scheduleLoads (m := 4) (braunSeq 0) braunAssign0 3 ≤ braunF 0 := by
  rw [braunAssign0_loads_decomp 3]
  have hL0 := braunL0Assign_loads
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 3 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunS0Assign0
    fin_cases i <;> decide
  have hF : scheduleLoads (m := 4) [braunF 0] (braunFAssign 0) 3 = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    unfold braunFAssign
    decide
  rw [hL0, hS0, hF]
  dsimp [braunL, braunS, braunF]
  nlinarith [braunα_gt_two]

lemma braunAssign0_makespan_le_F :
    makespan 4 (scheduleLoads (m := 4) (braunSeq 0) braunAssign0) ≤ braunF 0 := by
  dsimp [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  fin_cases j
  · exact le_of_eq braunAssign0_load_M0
  · exact le_of_eq braunAssign0_load_M1
  · exact le_of_eq braunAssign0_load_M2
  · exact braunAssign0_load_M3_le

/-- OPT of σ_r is at most F (Table-7 packing upper bound). -/
theorem braun_opt_le_F (r : ℕ) :
    optMakespan (m := 4) (braunSeq r) ≤ braunF r := by
  by_cases hr : r = 0
  · subst hr
    have hle := optMakespan_le_of_schedule (m := 4) (braunSeq 0)
      (scheduleLoads (m := 4) (braunSeq 0) braunAssign0) braunAssign0 rfl
    exact le_trans hle braunAssign0_makespan_le_F
  · have hge : 1 ≤ r := by omega
    have hle := optMakespan_le_of_schedule (m := 4) (braunSeq r)
      (scheduleLoads (m := 4) (braunSeq r) (braunAssign r)) (braunAssign r) rfl
    have hm : makespan 4 (scheduleLoads (m := 4) (braunSeq r) (braunAssign r)) ≤ braunF r := by
      dsimp [makespan]
      refine Finset.sup'_le _ _ (fun j hj => ?_)
      fin_cases j
      · exact le_of_eq (braun_load_M0_eq_F r)
      · exact le_of_eq (braun_load_M1_eq_F r)
      · exact le_of_eq (braun_load_M2_eq_F r hge)
      · exact le_of_lt (braun_load_M3_lt_F r hge)
    exact le_trans hle hm

/-- OPT(σ_r) = F. -/
theorem braun_opt_eq_F (r : ℕ) :
    optMakespan (m := 4) (braunSeq r) = braunF r := by
  apply le_antisymm
  · exact braun_opt_le_F r
  · exact braun_opt_ge_F r

/-! ### Forced scheduling: layer separation (v2, no OPT) -/

/-- Loads after `t` identical jobs of size `x` on top of a `base + k·x` start remain
    of that form (the multiples structure is preserved). -/
private lemma braun_loads_multiples_from_base (alg : OnlineAlgorithm 4) (base x : ℝ) :
    ∀ (t : ℕ) (loads_start : Loads 4)
      (h_start : ∀ i, ∃ k : ℕ, loads_start i = base + (k : ℝ) * x),
    ∀ i : Fin 4, ∃ k : ℕ,
      ((List.replicate t x).foldl (step (m := 4) alg) loads_start) i = base + (k : ℝ) * x := by
  intro t
  induction t with
  | zero => intro loads_start h_start i; exact h_start i
  | succ t ih =>
      intro loads_start h_start i
      have h_acc : ∀ j : Fin 4, ∃ k : ℕ,
          (step (m := 4) alg loads_start x) j = base + (k : ℝ) * x := by
        intro j
        dsimp [step]
        rcases h_start j with ⟨k, hk⟩
        split_ifs
        · simp [hk]
          exact ⟨k + 1, by push_cast; ring⟩
        · simp [hk]
      have h_final := ih (step (m := 4) alg loads_start x) h_acc i
      simpa [List.replicate_succ, List.foldl_cons] using h_final

/-- Four identical jobs of size `x` on a uniform base load force either an
    imbalanced makespan ≥ base + 2x, or perfect balance base + x on every machine. -/
lemma braun_layer_separation_from_base (alg : OnlineAlgorithm 4) (base x : ℝ) (hxpos : 0 < x)
    (loads_before : Loads 4) (h_uniform : ∀ i : Fin 4, loads_before i = base) :
    let loads_after := (List.replicate 4 x).foldl (step (m := 4) alg) loads_before
    makespan 4 loads_after ≥ base + 2 * x ∨
    (∀ i : Fin 4, loads_after i = base + x) := by
  intro loads_after
  have h_total_after : (∑ i : Fin 4, loads_after i) = (4 : ℝ) * (base + x) := by
    rw [show loads_after = (List.replicate 4 x).foldl (step (m := 4) alg) loads_before from rfl]
    rw [sum_foldl_step (m := 4) alg loads_before (List.replicate 4 x)]
    have h_sum_before : (∑ i : Fin 4, loads_before i) = (4 : ℝ) * base := by
      simp [h_uniform]
    rw [h_sum_before]
    simp [totalLoad]
    ring
  choose n hn using braun_loads_multiples_from_base alg base x 4 loads_before
    (by intro i; rw [h_uniform i]; exact ⟨0, by simp⟩)
  have h_sum_n_real : (∑ i : Fin 4, (n i : ℝ) * x) = (4 : ℝ) * x := by
    have h_all : (∑ i : Fin 4, (base + (n i : ℝ) * x)) = (4 : ℝ) * (base + x) := by
      calc
        (∑ i : Fin 4, (base + (n i : ℝ) * x)) = (∑ i : Fin 4, loads_after i) := by
          apply Finset.sum_congr rfl
          intro i hi
          change base + (n i : ℝ) * x =
            ((List.replicate 4 x).foldl (step (m := 4) alg) loads_before) i
          exact (hn i).symm
        _ = (4 : ℝ) * (base + x) := h_total_after
    have h_expand : (∑ i : Fin 4, (base + (n i : ℝ) * x)) =
        (4 : ℝ) * base + (∑ i : Fin 4, (n i : ℝ) * x) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand] at h_all
    nlinarith
  have h_sum_n : (∑ i : Fin 4, (n i : ℕ)) = 4 := by
    have h_cast_sum : (∑ i : Fin 4, ((n i : ℕ) : ℝ)) = (4 : ℝ) := by
      have h' : (∑ i : Fin 4, ((n i : ℕ) : ℝ)) * x = (4 : ℝ) * x := by
        simpa [Finset.sum_mul] using h_sum_n_real
      exact mul_right_cancel₀ (ne_of_gt hxpos) h'
    norm_num at h_cast_sum
    exact_mod_cast h_cast_sum
  by_cases h_exists : ∃ i, 2 ≤ n i
  · left
    rcases h_exists with ⟨i, hi⟩
    have h_load_ge : base + 2 * x ≤ loads_after i := by
      change base + 2 * x ≤ ((List.replicate 4 x).foldl (step (m := 4) alg) loads_before) i
      rw [hn i]
      have : (2 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hi
      nlinarith
    have h_makespan_ge : base + 2 * x ≤ makespan 4 loads_after := by
      have h := makespan_ge_each (m := 4) loads_after i
      linarith
    exact h_makespan_ge
  · right
    push_neg at h_exists
    have hn_le_one : ∀ i, n i ≤ 1 := by intro i; have h := h_exists i; omega
    have hn_all_one : ∀ i, n i = 1 := by
      intro i
      exact pigeonhole_all_ones (m := 4) n hn_le_one h_sum_n i
    intro i
    change ((List.replicate 4 x).foldl (step (m := 4) alg) loads_before) i = base + x
    rw [hn i, hn_all_one i, Nat.cast_one, one_mul]

/-! ### Forced scheduling: the S⁺_k deviation trap (prefix additive identity) -/

/-- If the plus job S⁺_k (k ≥ 1) is placed on a machine already carrying
    Φ_k = Σ_{i≤k}(L_i + S_i), the resulting makespan Φ_k + S⁺_k equals exactly
    √3·(S⁺_k + L_k) − (2 − √3), the forced competitive ratio. -/
lemma braun_prefix_additive_identity (k : ℕ) (hk : 1 ≤ k) :
    braunSumLS k + braunSp k = Real.sqrt 3 * (braunSp k + braunL k) - (2 - Real.sqrt 3) := by
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  have hq : braunQ - 1 ≠ 0 := braunQ_sub_one_ne_zero
  have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have hqk_comm : braunQ * braunQ ^ (k - 1) = braunQ ^ k := by
    rw [mul_comm]
    exact hqk.symm
  have hqsucc : braunQ ^ (k + 1) = braunQ ^ (k - 1) * (braunQ * braunQ) := by
    conv_lhs => rw [show k + 1 = (k - 1) + 2 from by omega]
    rw [pow_succ, pow_succ]
    ring
  have hc0 : (1 + braunα) / (braunQ - 1) = 3 - braunα := by
    have h : (3 - braunα) * (braunQ - 1) = 1 + braunα := by
      dsimp [braunQ]
      nlinarith [braun_poly2]
    rw [← h]
    field_simp [hq]
  have hc1 : (1 + braunα) * braunQ ^ 2 / (braunQ - 1) + braunα * braunQ + 2 * braunα =
      (braunα - 1) * ((braunα + 1) * braunQ + 2 * braunα) := by
    field_simp [hq]
    dsimp [braunQ]
    have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
    have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
      calc
        braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
        _ = braunα * (2 * braunα + 2) := by rw [hα2]
        _ = 2 * braunα ^ 2 + 2 * braunα := by ring
        _ = 6 * braunα + 4 := by rw [hα2]; ring
    have hα4 : braunα ^ 4 = 16 * braunα + 12 := by
      calc
        braunα ^ 4 = braunα * braunα ^ 3 := by rw [pow_succ']
        _ = braunα * (6 * braunα + 4) := by rw [hα3]
        _ = 6 * braunα ^ 2 + 4 * braunα := by ring
        _ = 16 * braunα + 12 := by rw [hα2]; ring
    have hα5 : braunα ^ 5 = 44 * braunα + 32 := by
      calc
        braunα ^ 5 = braunα * braunα ^ 4 := by rw [pow_succ']
        _ = braunα * (16 * braunα + 12) := by rw [hα4]
        _ = 16 * braunα ^ 2 + 12 * braunα := by ring
        _ = 44 * braunα + 32 := by rw [hα2]; ring
    have hα6 : braunα ^ 6 = 120 * braunα + 88 := by
      calc
        braunα ^ 6 = braunα * braunα ^ 5 := by rw [pow_succ']
        _ = braunα * (44 * braunα + 32) := by rw [hα5]
        _ = 44 * braunα ^ 2 + 32 * braunα := by ring
        _ = 120 * braunα + 88 := by rw [hα2]; ring
    ring_nf
    nlinarith [hα2, hα3, hα4, hα5, hα6]
  calc
    braunSumLS k + braunSp k
        = (1 + braunα) * braunSumL k + braunSp k := by rw [braunSumLS_eq]
    _ = (1 + braunα) * ((braunQ ^ (k + 1) - 1) / (braunQ - 1)) +
          (braunα * braunQ ^ k + 2 * braunα * braunQ ^ (k - 1)) := by
          rw [braun_geom_sum]
          dsimp [braunSp, braunS, braunL]
          ring
    _ = ((1 + braunα) * braunQ ^ 2 / (braunQ - 1) + braunα * braunQ + 2 * braunα) * braunQ ^ (k - 1) -
          (1 + braunα) / (braunQ - 1) := by
          rw [hqsucc, hqk]
          field_simp [hq]
          ring
    _ = (braunα - 1) * ((braunα + 1) * braunQ + 2 * braunα) * braunQ ^ (k - 1) - (3 - braunα) := by
          rw [hc1, hc0]
    _ = (braunα - 1) * ((braunα + 1) * braunQ ^ k + 2 * braunα * braunQ ^ (k - 1)) - (3 - braunα) := by
          rw [← hqk_comm]
          ring
    _ = (braunα - 1) * (braunSp k + braunL k) - (3 - braunα) := by
          dsimp [braunSp, braunS, braunL]
          ring
    _ = Real.sqrt 3 * (braunSp k + braunL k) - (2 - Real.sqrt 3) := by
          rw [← hs3, ← braun_two_sub_sqrt3]

/-- The prefix of σ_r through the plus job S⁺_k (k ≥ 1), defined recursively so that
    `braunPrefixSp (k+1) = braunPrefixSp k ++ braunLayerBlock (k+1)` holds by rfl. -/
def braunPrefixSp : ℕ → JobSequence
  | 0 => List.replicate 4 (braunL 0) ++ List.replicate 4 (braunS 0)
  | k + 1 => braunPrefixSp k ++ braunLayerBlock (k + 1)

lemma braunPrefixSp_length (k : ℕ) : (braunPrefixSp k).length = 8 * k + 8 := by
  induction k with
  | zero => simp [braunPrefixSp]
  | succ k ih =>
      dsimp only [braunPrefixSp]
      rw [List.length_append, ih, braunLayerBlock_length]
      omega

/-- The recursive prefix equals the flat L₀×4 ++ S₀×4 ++ blocks form. -/
lemma braunPrefixSp_eq_flat (k : ℕ) :
    braunPrefixSp k = List.replicate 4 (braunL 0) ++ List.replicate 4 (braunS 0) ++ braunBlocks k := by
  induction k with
  | zero => dsimp only [braunPrefixSp, braunBlocks]; simp
  | succ k ih =>
      dsimp only [braunPrefixSp, braunBlocks]
      rw [ih]
      simp only [List.append_assoc]

lemma braunPrefixSp_total (k : ℕ) :
    totalLoad (braunPrefixSp k) = totalLoad (braunSeq k) - braunF k := by
  rw [braunPrefixSp_eq_flat]
  dsimp only [totalLoad]
  rw [braunSeq_sum_decomp]
  simp only [List.sum_append, List.sum_replicate]
  ring

/-! ### Table 6: OPT of the prefix through S⁺_k equals S⁺_k + L_k -/

/-- Top-layer block assignment (Table 6): L_k one per machine, S_k to M1/M2/M3,
    S⁺_k to M0. -/
noncomputable def braunTopBlockAssign (k : ℕ) : Fin (braunLayerBlock k).length → Fin 4 :=
  fun i =>
    if i.1 = 0 then 0
    else if i.1 = 1 then 1
    else if i.1 = 2 then 2
    else if i.1 = 3 then 3
    else if i.1 = 4 then 1
    else if i.1 = 5 then 2
    else if i.1 = 6 then 3
    else 0

lemma braunTopBlockAssign_loads (k : ℕ) :
    scheduleLoads (m := 4) (braunLayerBlock k) (braunTopBlockAssign k) 0 = braunL k + braunSp k ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunTopBlockAssign k) 1 = braunL k + braunS k ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunTopBlockAssign k) 2 = braunL k + braunS k ∧
    scheduleLoads (m := 4) (braunLayerBlock k) (braunTopBlockAssign k) 3 = braunL k + braunS k := by
  unfold braunLayerBlock braunTopBlockAssign
  simp [scheduleLoads, Fin.sum_univ_succ]
  repeat (constructor <;> try ring) <;> trivial

/-- S₀ → M1/M3 base + blocks 1..r with top layer k: the Table-7 lower part. -/
noncomputable def braunAssignPrefixR (k r : ℕ) : Fin (braunPrefixSp r).length → Fin 4 :=
  match r with
  | 0 => appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0))
      braunL0Assign braunS0Assign
  | r + 1 => appendAssign (m := 4) (braunPrefixSp r) (braunLayerBlock (r + 1))
      (braunAssignPrefixR k r) (braunBlockAssign k (r + 1))

/-- Loads of `braunAssignPrefixR k r` (closed forms, induction on r). -/
lemma braunAssignPrefixR_loads (k r : ℕ) :
    scheduleLoads (m := 4) (braunPrefixSp r) (braunAssignPrefixR k r) 0 = 0 ∧
    scheduleLoads (m := 4) (braunPrefixSp r) (braunAssignPrefixR k r) 1 =
      2 * braunS 0 + (∑ t ∈ Finset.range r, (braunSp (t + 1) + 2 * braunL (t + 1))) ∧
    scheduleLoads (m := 4) (braunPrefixSp r) (braunAssignPrefixR k r) 2 =
      (∑ t ∈ Finset.range r, (if t + 1 = k then 2 * braunS (t + 1) else 0)) ∧
    scheduleLoads (m := 4) (braunPrefixSp r) (braunAssignPrefixR k r) 3 =
      4 * braunL 0 + 2 * braunS 0 +
        (∑ t ∈ Finset.range r, (2 * braunL (t + 1) + (if t + 1 = k then braunS (t + 1) else 3 * braunS (t + 1)))) := by
  induction r with
  | zero =>
      simp only [braunAssignPrefixR, braunPrefixSp]
      repeat (rw [scheduleLoads_append])
      have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 0 = 0 := by
        apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
      have hL1 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 1 = 0 := by
        apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
      have hL2 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 2 = 0 := by
        apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
      have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 0 = 0 := by
        apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunS0Assign; fin_cases i <;> decide
      have hS2 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign 2 = 0 := by
        apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunS0Assign; fin_cases i <;> decide
      rw [hL0, hL1, hL2, hS0, hS2]
      constructor
      · ring
      constructor
      · rw [braunS0Assign_loads.1]; ring
      constructor
      · ring
      · rw [braunL0Assign_loads, braunS0Assign_loads.2]; ring
  | succ r ih =>
      simp only [braunAssignPrefixR, braunPrefixSp]
      repeat (rw [scheduleLoads_append])
      rcases ih with ⟨ih0, ih1, ih2, ih3⟩
      rcases braunBlockAssign_loads k (r + 1) with ⟨hb0, hb1, hb2, hb3⟩
      constructor
      · rw [ih0, hb0]; ring
      constructor
      · rw [ih1, hb1]
        rw [Finset.sum_range_succ]
        ring
      constructor
      · rw [ih2, hb2]
        rw [Finset.sum_range_succ]
      · rw [ih3, hb3]
        rw [Finset.sum_range_succ]
        by_cases h : r + 1 = k
        · simp [h]
          ring
        · have h' : k ≠ r + 1 := fun hk => h hk.symm
          simp [h, h']
          ring

/-- Lower-prefix loads with top = k: M0 = 0, M1 = M2 = 2S_k, M3 < 2S_k (k ≥ 1). -/
lemma braunAssignPrefixR_loads_top (k : ℕ) (hk : 1 ≤ k) :
    scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 0 = 0 ∧
    scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 1 = 2 * braunS k ∧
    scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 2 = 2 * braunS k ∧
    scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 3 < 2 * braunS k := by
  rcases braunAssignPrefixR_loads k k with ⟨h0, h1, h2, h3⟩
  have hsumM2 : (∑ t ∈ Finset.range k, (if t + 1 = k then 2 * braunS (t + 1) else 0)) = 2 * braunS k := by
    refine Eq.trans (Finset.sum_eq_single_of_mem (k - 1) ?hmem ?h₀) ?hmain
    · exact Finset.mem_range.mpr (Nat.sub_lt (Nat.succ_le_iff.mp hk) (by norm_num : 0 < 1))
    · intro b hb hne
      have hb1 : b + 1 ≠ k := by
        intro h
        exact hne (by omega)
      simp [hb1]
    · rw [Nat.sub_add_cancel hk]
      simp
  constructor
  · exact h0
  constructor
  · rw [h1]
    rw [add_comm]
    rw [braun_M1_eq_F k]
    rfl
  constructor
  · rw [h2, hsumM2]
  · -- M3 = total - M0 - M1 - M2 = (3F - c) - F - F = F - c < F = 2S_k
    have hsum := sum_scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k)
    have h3' := fin4_sum_extract3 (fun j => scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) j)
    have hM1 : scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 1 = 2 * braunS k := by
      rw [h1]
      rw [add_comm]
      rw [braun_M1_eq_F k]
      rfl
    have hM2 : scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 2 = 2 * braunS k := by
      rw [h2, hsumM2]
    rw [show scheduleLoads (m := 4) (braunPrefixSp k) (braunAssignPrefixR k k) 3 =
        totalLoad (braunPrefixSp k) - 2 * braunS k - 2 * braunS k by
      rw [h3']
      rw [hsum]
      rw [h0, hM1, hM2]
      ring]
    rw [braunPrefixSp_total k]
    rw [braun_total_work k]
    dsimp [braunF]
    have hc : 0 < (4 + 6 * braunα) / (braunQ - 1) := by
      have hnum : 0 < 4 + 6 * braunα := by nlinarith [braunα_pos]
      have hden : 0 < braunQ - 1 := by linarith [braunQ_gt_one]
      positivity
    nlinarith

/-- Full Table-6 assignment of the prefix through S⁺_k. -/
noncomputable def braunPrefixAssign (k : ℕ) : Fin (braunPrefixSp k).length → Fin 4 :=
  match k with
  | 0 => appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0))
      braunL0Assign braunS0Assign0
  | 1 => appendAssign (m := 4) (braunPrefixSp 0) (braunLayerBlock 1)
      (braunPrefixAssign 0) (braunTopBlockAssign 1)
  | k + 2 => appendAssign (m := 4) (braunPrefixSp (k + 1)) (braunLayerBlock (k + 2))
      (braunAssignPrefixR (k + 1) (k + 1)) (braunTopBlockAssign (k + 2))

/-- Base loads of `braunPrefixAssign 0` (S₀ → M1/M2). -/
lemma braunPrefixAssign_base_loads :
    scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 0 = 0 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 1 = 2 * braunS 0 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 2 = 2 * braunS 0 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 3 = 4 * braunL 0 := by
  simp only [braunPrefixAssign, braunPrefixSp]
  repeat (rw [scheduleLoads_append])
  have hL0 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
  have hL1 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 1 = 0 := by
    apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
  have hL2 : scheduleLoads (m := 4) (List.replicate 4 (braunL 0)) braunL0Assign 2 = 0 := by
    apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunL0Assign; decide
  have hS0 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 0 = 0 := by
    apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunS0Assign0; fin_cases i <;> decide
  have hS3 : scheduleLoads (m := 4) (List.replicate 4 (braunS 0)) braunS0Assign0 3 = 0 := by
    apply scheduleLoads_zero_of_forall_ne; intro i; unfold braunS0Assign0; fin_cases i <;> decide
  rw [hL0, hL1, hL2, hS0, hS3]
  constructor
  · ring
  constructor
  · rw [braunS0Assign0_loads.1]; ring
  constructor
  · rw [braunS0Assign0_loads.2]; ring
  · rw [braunL0Assign_loads]; ring

/-- Loads of the Table-6 prefix assignment: every machine ≤ S⁺_k + L_k. -/
lemma braunPrefixAssign_makespan_le (k : ℕ) (hk : 1 ≤ k) :
    makespan 4 (scheduleLoads (m := 4) (braunPrefixSp k) (braunPrefixAssign k)) ≤ braunSp k + braunL k := by
  dsimp [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  by_cases hk1 : k = 1
  · subst hk1
    have hdec (j : Fin 4) :
        scheduleLoads (m := 4) (braunPrefixSp 1) (braunPrefixAssign 1) j =
        scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) j +
        scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) j := by
      unfold braunPrefixAssign
      change scheduleLoads (m := 4) (braunPrefixSp 0 ++ braunLayerBlock 1)
        (appendAssign (m := 4) (braunPrefixSp 0) (braunLayerBlock 1) (braunPrefixAssign 0) (braunTopBlockAssign 1)) j =
        scheduleLoads (m := 4) (braunPrefixSp 0)
          (appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0)) braunL0Assign braunS0Assign0) j +
        scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) j
      rw [scheduleLoads_append]
      simp only [braunPrefixAssign]
    rw [hdec j]
    rcases braunPrefixAssign_base_loads with ⟨hl0, hl1, hl2, hl3⟩
    rcases braunTopBlockAssign_loads 1 with ⟨ht0, ht1, ht2, ht3⟩
    fin_cases j
    · change scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 0 +
          scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) 0 ≤ braunSp 1 + braunL 1
      rw [hl0, ht0]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 1 +
          scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) 1 ≤ braunSp 1 + braunL 1
      rw [hl1, ht1]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 2 +
          scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) 2 ≤ braunSp 1 + braunL 1
      rw [hl2, ht2]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp 0) (braunPrefixAssign 0) 3 +
          scheduleLoads (m := 4) (braunLayerBlock 1) (braunTopBlockAssign 1) 3 ≤ braunSp 1 + braunL 1
      rw [hl3, ht3]
      dsimp [braunSp, braunS, braunL]
      nlinarith [braunα_gt_two]
  · rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
    have hk' : 1 ≤ k' := by omega
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : k' ≠ 0) with ⟨k'', rfl⟩
    have hdec (j : Fin 4) :
        scheduleLoads (m := 4) (braunPrefixSp (k'' + 2)) (braunPrefixAssign (k'' + 2)) j =
        scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) j +
        scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) j := by
      change scheduleLoads (m := 4) (braunPrefixSp (k'' + 1) ++ braunLayerBlock (k'' + 2))
        (braunPrefixAssign (k'' + 2)) j =
        scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) j +
        scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) j
      rw [show braunPrefixAssign (k'' + 2) =
          appendAssign (m := 4) (braunPrefixSp (k'' + 1)) (braunLayerBlock (k'' + 2))
            (braunAssignPrefixR (k'' + 1) (k'' + 1)) (braunTopBlockAssign (k'' + 2)) by
        simp only [braunPrefixAssign]
        rfl]
      rw [scheduleLoads_append]
    rw [hdec j]
    rcases braunAssignPrefixR_loads_top (k'' + 1) (by omega) with ⟨hl0, hl1, hl2, hl3⟩
    rcases braunTopBlockAssign_loads (k'' + 2) with ⟨ht0, ht1, ht2, ht3⟩
    fin_cases j
    · change scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) 0 +
          scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) 0 ≤
          braunSp (k'' + 2) + braunL (k'' + 2)
      rw [hl0, ht0]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) 1 +
          scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) 1 ≤
          braunSp (k'' + 2) + braunL (k'' + 2)
      rw [hl1, ht1]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) 2 +
          scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) 2 ≤
          braunSp (k'' + 2) + braunL (k'' + 2)
      rw [hl2, ht2]
      dsimp [braunSp, braunS, braunL]
      nlinarith
    · change scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) 3 +
          scheduleLoads (m := 4) (braunLayerBlock (k'' + 2)) (braunTopBlockAssign (k'' + 2)) 3 ≤
          braunSp (k'' + 2) + braunL (k'' + 2)
      rw [ht3]
      have hlt : scheduleLoads (m := 4) (braunPrefixSp (k'' + 1)) (braunAssignPrefixR (k'' + 1) (k'' + 1)) 3 < 2 * braunS (k'' + 1) := hl3
      dsimp [braunSp, braunS, braunL] at hlt ⊢
      nlinarith [hlt]

/-- OPT of the prefix through S⁺_k is at most S⁺_k + L_k (Table 6 upper bound). -/
theorem braun_opt_prefix_Sp_le (k : ℕ) (hk : 1 ≤ k) :
    optMakespan (m := 4) (braunPrefixSp k) ≤ braunSp k + braunL k := by
  have hle := optMakespan_le_of_schedule (m := 4) (braunPrefixSp k)
    (scheduleLoads (m := 4) (braunPrefixSp k) (braunPrefixAssign k)) (braunPrefixAssign k) rfl
  exact le_trans hle (braunPrefixAssign_makespan_le k hk)

/-! ### Table 6 lower bound: OPT of the prefix through S⁺_k is at least S⁺_k + L_k -/

/-- The load of a concatenated sequence under an arbitrary assignment splits into the
    loads of both pieces under the induced assignments. -/
lemma scheduleLoads_split_append (σ τ : JobSequence)
    (a : Fin (σ ++ τ).length → Fin 4) (j : Fin 4) :
    scheduleLoads (m := 4) (σ ++ τ) a j =
      scheduleLoads (m := 4) σ (fun i => a ⟨i.1, by
        simp only [List.length_append]
        omega⟩) j +
      scheduleLoads (m := 4) τ (fun i => a ⟨σ.length + i.1, by
        simp only [List.length_append]
        omega⟩) j := by
  induction σ with
  | nil =>
      dsimp only [scheduleLoads]
      simp
  | cons p σ ih =>
      let aσ : Fin (p :: σ).length → Fin 4 := fun i => a ⟨i.1, by
        simp only [List.length_append, List.length_cons]
        omega⟩
      let aτ : Fin τ.length → Fin 4 := fun i => a ⟨(p :: σ).length + i.1, by
        simp only [List.length_append, List.length_cons]
        omega⟩
      change scheduleLoads (m := 4) (p :: (σ ++ τ)) a j =
        scheduleLoads (m := 4) (p :: σ) aσ j + scheduleLoads (m := 4) τ aτ j
      rw [scheduleLoads_cons (m := 4) p (σ ++ τ) a j]
      rw [show scheduleLoads (m := 4) (p :: σ) aσ j =
          (if a ⟨0, by simp⟩ = j then p else 0) + scheduleLoads (m := 4) σ (aσ ∘ Fin.succ) j by
        rw [scheduleLoads_cons (m := 4) p σ aσ j]
        rfl]
      rw [ih (a ∘ Fin.succ)]
      have hσp : aσ ∘ Fin.succ =
          (fun i : Fin σ.length => (a ∘ Fin.succ) ⟨i.1, by
            have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
            omega⟩) := by
        funext i
        rfl
      rw [hσp]
      have hshift : (fun i : Fin τ.length => (a ∘ Fin.succ) ⟨σ.length + i.1, by
          have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
          omega⟩) =
        (fun i : Fin τ.length => a ⟨(p :: σ).length + i.1, by
          simp only [List.length_append, List.length_cons]
          omega⟩) := by
        funext i
        change a (Fin.succ ⟨σ.length + i.1, by
            have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
            omega⟩) =
          a ⟨(p :: σ).length + i.1, by
            simp only [List.length_append, List.length_cons]
            omega⟩
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        have hcons : (p :: σ).length = σ.length + 1 := by simp only [List.length_cons]
        omega
      dsimp only [aτ]
      rw [← hshift]
      change (if a ⟨0, by simp⟩ = j then p else 0) +
          (scheduleLoads (m := 4) σ (fun i => (a ∘ Fin.succ) ⟨i.1, by
            have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
            omega⟩) j +
            scheduleLoads (m := 4) τ (fun i => (a ∘ Fin.succ) ⟨σ.length + i.1, by
              have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
              omega⟩) j) =
        (if a ⟨0, by simp⟩ = j then p else 0) +
          scheduleLoads (m := 4) σ (fun i => (a ∘ Fin.succ) ⟨i.1, by
            have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
            omega⟩) j +
          scheduleLoads (m := 4) τ (fun i => (a ∘ Fin.succ) ⟨σ.length + i.1, by
            have hlen : (List.append σ τ).length = σ.length + τ.length := by simp
            omega⟩) j
      ring

/-- The load of four identical jobs under an assignment equals the number of
    jobs placed on j times the job size. -/
lemma scheduleLoads_replicate4_eq_count (x : ℝ) (a : Fin 4 → Fin 4) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 4 x) a j =
      ((Finset.univ : Finset (Fin 4)).filter (fun i => a i = j)).card * x := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 4, if a i = j then (List.replicate 4 x)[i] else 0) =
    ((Finset.univ : Finset (Fin 4)).filter (fun i => a i = j)).card * x
  rw [Fin.sum_univ_four]
  conv_lhs => simp
  rw [show ((Finset.univ : Finset (Fin 4)).filter (fun i => a i = j)).card =
      (∑ i : Fin 4, (if a i = j then (1 : ℕ) else 0)) by
    rw [Finset.card_filter]]
  rw [Fin.sum_univ_four]
  by_cases h0 : a 0 = j <;> by_cases h1 : a 1 = j <;> by_cases h2 : a 2 = j <;> by_cases h3 : a 3 = j <;>
    simp [h0, h1, h2, h3]
  all_goals ring

/-- The load of three identical jobs under an assignment equals the number of
    jobs placed on j times the job size. -/
lemma scheduleLoads_replicate3_eq_count (x : ℝ) (a : Fin 3 → Fin 4) (j : Fin 4) :
    scheduleLoads (m := 4) (List.replicate 3 x) a j =
      ((Finset.univ : Finset (Fin 3)).filter (fun i => a i = j)).card * x := by
  dsimp only [scheduleLoads]
  change (∑ i : Fin 3, if a i = j then (List.replicate 3 x)[i] else 0) =
    ((Finset.univ : Finset (Fin 3)).filter (fun i => a i = j)).card * x
  rw [Fin.sum_univ_three]
  conv_lhs => simp
  rw [show ((Finset.univ : Finset (Fin 3)).filter (fun i => a i = j)).card =
      (∑ i : Fin 3, (if a i = j then (1 : ℕ) else 0)) by
    rw [Finset.card_filter]]
  rw [Fin.sum_univ_three]
  by_cases h0 : a 0 = j <;> by_cases h1 : a 1 = j <;> by_cases h2 : a 2 = j <;>
    simp [h0, h1, h2]
  all_goals ring

/-- The load of a single job. -/
lemma scheduleLoads_singleton (x : ℝ) (a : Fin 1 → Fin 4) (j : Fin 4) :
    scheduleLoads (m := 4) [x] a j = if a 0 = j then x else 0 := by
  simp [scheduleLoads]

/-- OPT of a concatenation is at least the OPT of its suffix (nonnegative prefix). -/
lemma optMakespan_suffix_ge (σ τ : JobSequence) (hσ : ∀ p ∈ σ, 0 ≤ p) :
    optMakespan (m := 4) τ ≤ optMakespan (m := 4) (σ ++ τ) := by
  apply Finset.le_inf'
  intro a _
  let aσ : Fin σ.length → Fin 4 := fun i => a ⟨i.1, by
    have hlen : (σ ++ τ).length = σ.length + τ.length := by simp
    rw [hlen]; omega⟩
  let aτ : Fin τ.length → Fin 4 := fun i => a ⟨σ.length + i.1, by
    have hlen : (σ ++ τ).length = σ.length + τ.length := by simp
    rw [hlen]; omega⟩
  have hmk : makespan 4 (scheduleLoads (m := 4) τ aτ) ≤ makespan 4 (scheduleLoads (m := 4) (σ ++ τ) a) := by
    dsimp only [makespan]
    refine Finset.sup'_le _ _ (fun j hj => ?_)
    have hsplit := scheduleLoads_split_append σ τ a j
    have hnonneg : 0 ≤ scheduleLoads (m := 4) σ aσ j := by
      dsimp only [scheduleLoads]
      apply Finset.sum_nonneg
      intro i hi
      by_cases h : aσ i = j
      · rw [if_pos h]
        exact hσ σ[i] (List.mem_iff_getElem.mpr ⟨i.1, i.2, rfl⟩)
      · rw [if_neg h]
    have hle_j : scheduleLoads (m := 4) τ aτ j ≤ scheduleLoads (m := 4) (σ ++ τ) a j := by
      rw [hsplit]
      linarith
    exact le_trans hle_j (makespan_ge_each (m := 4) (scheduleLoads (m := 4) (σ ++ τ) a) j)
  exact le_trans (optMakespan_le_schedule (m := 4) τ aτ) hmk

/-- All jobs of one layer block are nonnegative. -/
lemma braunLayerBlock_nonneg (k : ℕ) : ∀ p ∈ braunLayerBlock k, 0 ≤ p := by
  intro p hp
  unfold braunLayerBlock at hp
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hp
  rcases hp with hLS | hSp
  · rcases hLS with ⟨_, hL⟩ | ⟨_, hS⟩
    · rw [hL]; exact le_of_lt (braunL_pos k)
    · rw [hS]; exact le_of_lt (braunS_pos k)
  · rw [hSp]; exact le_of_lt (braunSp_pos k)

/-- All jobs of the prefix are nonnegative. -/
lemma braunPrefixSp_nonneg (r : ℕ) : ∀ p ∈ braunPrefixSp r, 0 ≤ p := by
  induction r with
  | zero =>
      dsimp only [braunPrefixSp]
      intro p hp
      simp only [List.mem_append, List.mem_replicate] at hp
      rcases hp with ⟨_, hL⟩ | ⟨_, hS⟩
      · rw [hL]; exact le_of_lt (braunL_pos 0)
      · rw [hS]; exact le_of_lt (braunS_pos 0)
  | succ r ih =>
      dsimp only [braunPrefixSp]
      intro p hp
      simp only [List.mem_append] at hp
      rcases hp with hpre | hblk
      · exact ih p hpre
      · exact braunLayerBlock_nonneg (r + 1) p hblk

/-- S⁺_k ≥ S_k: the plus job is at least as large as a regular S job. -/
lemma braunS_le_braunSp (k : ℕ) : braunS k ≤ braunSp k := by
  dsimp [braunSp]
  have h : 0 ≤ 2 * braunS (k - 1) := by nlinarith [braunS_pos (k - 1)]
  linarith

/-- 2·S_k ≥ S⁺_k + L_k (k ≥ 1): two S-layer jobs already reach the bound. -/
lemma braun_twoS_ge_bound (k : ℕ) (hk : 1 ≤ k) :
    braunSp k + braunL k ≤ 2 * braunS k := by
  have hdiff : 2 * braunS k - (braunSp k + braunL k) =
      2 * braunα * (braunα + 1) * braunQ ^ (k - 1) := by
    dsimp [braunSp, braunS, braunL]
    have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
    have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
      calc
        braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
        _ = braunα * (2 * braunα + 2) := by rw [hα2]
        _ = 2 * braunα ^ 2 + 2 * braunα := by ring
        _ = 6 * braunα + 4 := by rw [hα2]; ring
    have hmain : 2 * braunα * braunQ - (braunα * braunQ + 2 * braunα + braunQ) =
        2 * braunα * (braunα + 1) := by
      dsimp [braunQ]
      nlinarith [hα2, hα3]
    calc
      2 * (braunα * braunQ ^ k) - (braunα * braunQ ^ k + 2 * (braunα * braunQ ^ (k - 1)) + braunQ ^ k)
          = (2 * braunα * braunQ - (braunα * braunQ + 2 * braunα + braunQ)) * braunQ ^ (k - 1) := by
            rw [hqk]
            ring
      _ = 2 * braunα * (braunα + 1) * braunQ ^ (k - 1) := by rw [hmain]
  have hpos : 0 ≤ 2 * braunα * (braunα + 1) * braunQ ^ (k - 1) := by
    have h1 : 0 ≤ 2 * braunα * (braunα + 1) := by
      exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt braunα_pos))
        (by linarith [braunα_pos])
    have h3 : 0 ≤ braunQ ^ (k - 1) := pow_nonneg (le_of_lt braunQ_pos) (k - 1)
    exact mul_nonneg h1 h3
  have hshift : 0 ≤ 2 * braunS k - (braunSp k + braunL k) := by
    rw [hdiff]
    exact hpos
  linarith

/-- S_k + 2·L_k ≥ S⁺_k + L_k (k ≥ 1): one S job plus two L jobs reach the bound. -/
lemma braun_S_twoL_ge_bound (k : ℕ) (hk : 1 ≤ k) :
    braunSp k + braunL k ≤ braunS k + 2 * braunL k := by
  have hdiff : braunS k + 2 * braunL k - (braunSp k + braunL k) =
      2 * braunα * (braunα - 1) * braunQ ^ (k - 1) := by
    dsimp [braunSp, braunS, braunL]
    have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
    have hmain : braunα * braunQ + 2 * braunQ - (braunα * braunQ + 2 * braunα + braunQ) =
        2 * braunα * (braunα - 1) := by
      dsimp [braunQ]
      nlinarith [hα2]
    calc
      braunα * braunQ ^ k + 2 * braunQ ^ k - (braunα * braunQ ^ k + 2 * (braunα * braunQ ^ (k - 1)) + braunQ ^ k)
          = (braunα * braunQ + 2 * braunQ - (braunα * braunQ + 2 * braunα + braunQ)) * braunQ ^ (k - 1) := by
            rw [hqk]
            ring
      _ = 2 * braunα * (braunα - 1) * braunQ ^ (k - 1) := by rw [hmain]
  have hpos : 0 ≤ 2 * braunα * (braunα - 1) * braunQ ^ (k - 1) := by
    have h1 : 0 ≤ 2 * braunα * (braunα - 1) := by
      exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt braunα_pos))
        (by linarith [braunα_gt_two])
    have h3 : 0 ≤ braunQ ^ (k - 1) := pow_nonneg (le_of_lt braunQ_pos) (k - 1)
    exact mul_nonneg h1 h3
  have hshift : 0 ≤ braunS k + 2 * braunL k - (braunSp k + braunL k) := by
    rw [hdiff]
    exact hpos
  linarith

/-- Four counters summing to 4, one of them zero, force some counter ≥ 2. -/
lemma exists_two_of_sum_four (f : Fin 4 → ℕ) (jsp : Fin 4) (hjsp : f jsp = 0)
    (hsum : (∑ j : Fin 4, f j) = 4) : ∃ j : Fin 4, 2 ≤ f j := by
  by_contra h
  have hle : ∀ j : Fin 4, f j ≤ 1 := by
    intro j
    by_contra hj
    apply h ⟨j, by omega⟩
  rw [Fin.sum_univ_four] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  fin_cases jsp
  · have hjsp' : f 0 = 0 := by simpa using hjsp
    omega
  · have hjsp' : f 1 = 0 := by simpa using hjsp
    omega
  · have hjsp' : f 2 = 0 := by simpa using hjsp
    omega
  · have hjsp' : f 3 = 0 := by simpa using hjsp
    omega

/-- Four counters summing to 4, each ≤ 1, must all be exactly 1. -/
lemma eq_one_of_sum_four_le_one (f : Fin 4 → ℕ) (hle : ∀ j : Fin 4, f j ≤ 1)
    (hsum : (∑ j : Fin 4, f j) = 4) : ∀ j : Fin 4, f j = 1 := by
  intro j
  rw [Fin.sum_univ_four] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  fin_cases j
  · have hg : f 0 = 1 := by omega
    simpa using hg
  · have hg : f 1 = 1 := by omega
    simpa using hg
  · have hg : f 2 = 1 := by omega
    simpa using hg
  · have hg : f 3 = 1 := by omega
    simpa using hg

/-- The 8-job top block {S⁺_k, S_k³, L_k⁴} forces makespan ≥ S⁺_k + L_k under any
    assignment (k ≥ 1). Four S-layer jobs occupy the four machines, the S⁺_k machine
    cannot take an L_k job, and each S_k machine can take at most one L_k job — but
    there are four L_k jobs for the remaining three machines. -/
lemma braunLayerBlock_makespan_ge (k : ℕ) (hk : 1 ≤ k)
    (a : Fin (braunLayerBlock k).length → Fin 4) :
    braunSp k + braunL k ≤ makespan 4 (scheduleLoads (m := 4) (braunLayerBlock k) a) := by
  unfold braunLayerBlock at a ⊢
  let blk : JobSequence := List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k) ++ [braunSp k]
  change braunSp k + braunL k ≤ makespan 4 (scheduleLoads (m := 4) blk a)
  let cL : Fin 4 → ℕ := fun j => ((Finset.univ : Finset (Fin 4)).filter (fun i => a ⟨i.1, by simp; omega⟩ = j)).card
  let cS : Fin 4 → ℕ := fun j => ((Finset.univ : Finset (Fin 3)).filter (fun i => a ⟨4 + i.1, by simp; omega⟩ = j)).card
  let onSp : Fin 4 → Prop := fun j => a ⟨7, by simp⟩ = j
  have hload (j : Fin 4) :
      scheduleLoads (m := 4) blk a j =
        (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k + (if onSp j then braunSp k else 0) := by
    have hlen7 : (List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k)).length = 7 := by
      simp only [List.length_append, List.length_replicate]
    have hlen8 : (List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k) ++ [braunSp k]).length = 8 := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
    have h1 := scheduleLoads_split_append (List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k)) [braunSp k] a j
    have h2 := scheduleLoads_split_append (List.replicate 4 (braunL k)) (List.replicate 3 (braunS k))
      (fun i : Fin (List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k)).length => a ⟨i.1, by
        have hi7 : i.1 < 7 := by omega
        rw [hlen8]
        omega⟩) j
    dsimp only [blk]
    rw [h1, h2]
    change scheduleLoads (m := 4) (List.replicate 4 (braunL k)) (fun i : Fin 4 => a ⟨i.1, by
          have h4 : (List.replicate 4 (braunL k)).length = 4 := by simp only [List.length_replicate]
          rw [hlen8]
          omega⟩) j +
        scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => a ⟨4 + i.1, by
          have h3 : (List.replicate 3 (braunS k)).length = 3 := by simp only [List.length_replicate]
          rw [hlen8]
          omega⟩) j +
        scheduleLoads (m := 4) [braunSp k] (fun i : Fin 1 => a ⟨7 + i.1, by
          have h1' : [braunSp k].length = 1 := by simp only [List.length_singleton]
          rw [hlen8]
          omega⟩) j =
      (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k + (if onSp j then braunSp k else 0)
    rw [scheduleLoads_replicate4_eq_count (braunL k) (fun i : Fin 4 => a ⟨i.1, by
      have h4 : (List.replicate 4 (braunL k)).length = 4 := by simp only [List.length_replicate]
      rw [hlen8]
      omega⟩) j]
    rw [scheduleLoads_replicate3_eq_count (braunS k) (fun i : Fin 3 => a ⟨4 + i.1, by
      have h3 : (List.replicate 3 (braunS k)).length = 3 := by simp only [List.length_replicate]
      rw [hlen8]
      omega⟩) j]
    rw [scheduleLoads_singleton (braunSp k) (fun i : Fin 1 => a ⟨7 + i.1, by
      have h1' : [braunSp k].length = 1 := by simp only [List.length_singleton]
      rw [hlen8]
      omega⟩) j]
    dsimp only [cL, cS, onSp]
    rfl
  by_contra hlt
  have hmklt : makespan 4 (scheduleLoads (m := 4) blk a) < braunSp k + braunL k := lt_of_not_ge hlt
  have hload_lt (j : Fin 4) : scheduleLoads (m := 4) blk a j < braunSp k + braunL k :=
    lt_of_le_of_lt (makespan_ge_each (m := 4) (scheduleLoads (m := 4) blk a) j) hmklt
  -- two S-layer jobs on one machine already reach the bound
  have hcaseA (j : Fin 4) (h2 : 2 ≤ cS j + (if onSp j then 1 else 0)) : False := by
    have hloadge : 2 * braunS k ≤ scheduleLoads (m := 4) blk a j := by
      rw [hload j]
      by_cases hon : onSp j
      · -- the plus job S⁺_k sits here too: the if-term is braunSp k ≥ braunS k
        have hcast' : (2 : ℝ) ≤ (cS j : ℝ) + 1 := by
          have hc := h2
          simp only [hon, if_true] at hc
          exact_mod_cast hc
        have hcSmul : (2 : ℝ) * braunS k ≤ (cS j : ℝ) * braunS k + braunS k := by
          have hmul : (2 : ℝ) * braunS k ≤ ((cS j : ℝ) + 1) * braunS k :=
            mul_le_mul_of_nonneg_right hcast' (le_of_lt (braunS_pos k))
          nlinarith
        have hSpS : braunS k ≤ braunSp k := braunS_le_braunSp k
        have hcLnn : 0 ≤ (cL j : ℝ) * braunL k :=
          mul_nonneg (by exact_mod_cast Nat.zero_le (cL j)) (le_of_lt (braunL_pos k))
        simp only [hon, if_true]
        nlinarith [hcSmul, hSpS, hcLnn]
      · -- no plus job here: the if-term is 0, but two S_k jobs force the load
        have hcast' : (2 : ℝ) ≤ (cS j : ℝ) := by
          have hc := h2
          simp only [hon, if_false] at hc
          exact_mod_cast hc
        have hcSmul : (2 : ℝ) * braunS k ≤ (cS j : ℝ) * braunS k :=
          mul_le_mul_of_nonneg_right hcast' (le_of_lt (braunS_pos k))
        have hcLnn : 0 ≤ (cL j : ℝ) * braunL k :=
          mul_nonneg (by exact_mod_cast Nat.zero_le (cL j)) (le_of_lt (braunL_pos k))
        simp only [hon, if_false]
        nlinarith [hcSmul, hcLnn]
    have hge' : 2 * braunS k ≤ (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k + (if onSp j then braunSp k else 0) := by
      have h := hloadge
      rw [hload j] at h
      exact h
    have hlt' : (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k + (if onSp j then braunSp k else 0) < braunSp k + braunL k := by
      have h := hload_lt j
      rw [hload j] at h
      exact h
    nlinarith [hge', hlt', braun_twoS_ge_bound k hk]
  -- so each machine holds at most one S-layer job; there are four of them, so exactly one each
  have hle1 : ∀ j : Fin 4, cS j + (if onSp j then 1 else 0) ≤ 1 := by
    intro j
    by_contra h
    have h2 : 2 ≤ cS j + (if onSp j then 1 else 0) := by omega
    exact hcaseA j h2
  have hSsum : (∑ j : Fin 4, cS j) = 3 := by
    dsimp only [cS]
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin 3))) (f := fun i => a ⟨4 + i.1, by
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega⟩)
      (t := (Finset.univ : Finset (Fin 4))) (H := by intro x hx; simp)
    rw [← hfib]
    norm_num
  have hIndSum : (∑ j : Fin 4, (if onSp j then 1 else 0)) = 1 := by
    dsimp only [onSp]
    rw [show (∑ j : Fin 4, (if a ⟨7, by simp⟩ = j then (1 : ℕ) else 0)) =
        (∑ j ∈ (Finset.univ : Finset (Fin 4)), (if j = a ⟨7, by simp⟩ then (1 : ℕ) else 0)) by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : a ⟨7, by simp⟩ = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h'' => h h''.symm)]]
    rw [Finset.sum_ite_eq']
    simp
  have hgsum : (∑ j : Fin 4, (cS j + (if onSp j then 1 else 0))) = 4 := by
    rw [Finset.sum_add_distrib, hSsum, hIndSum]
  have hone : ∀ j : Fin 4, cS j + (if onSp j then 1 else 0) = 1 :=
    eq_one_of_sum_four_le_one _ hle1 hgsum
  let jsp : Fin 4 := a ⟨7, by simp⟩
  have honjsp : onSp jsp := by dsimp only [onSp, jsp]
  have hcS_jsp : cS jsp = 0 := by
    have h := hone jsp
    simp only [honjsp, if_true] at h
    omega
  -- the S⁺_k machine cannot take any L_k job
  have hcL_jsp : cL jsp = 0 := by
    by_contra h
    have h1 : 1 ≤ cL jsp := Nat.pos_of_ne_zero (fun hz => h hz)
    have hcaseB : False := by
      have hcLmul : braunL k ≤ (cL jsp : ℝ) * braunL k := by
        have hcLcast : (1 : ℝ) ≤ (cL jsp : ℝ) := by exact_mod_cast h1
        simpa using mul_le_mul_of_nonneg_right hcLcast (le_of_lt (braunL_pos k))
      have hcS0 : (cS jsp : ℝ) * braunS k = 0 := by
        have hcS0' : (cS jsp : ℝ) = 0 := by exact_mod_cast hcS_jsp
        rw [hcS0', zero_mul]
      have hge : braunSp k + braunL k ≤ (cL jsp : ℝ) * braunL k + (cS jsp : ℝ) * braunS k + braunSp k := by
        nlinarith [hcLmul, hcS0]
      have hlt : (cL jsp : ℝ) * braunL k + (cS jsp : ℝ) * braunS k + braunSp k < braunSp k + braunL k := by
        have h := hload_lt jsp
        rw [hload jsp] at h
        simpa only [honjsp, if_true] using h
      nlinarith
    exact hcaseB
  -- hence the four L_k jobs sit on the other three machines: some machine has two
  have hLsum : (∑ j : Fin 4, cL j) = 4 := by
    dsimp only [cL]
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin 4))) (f := fun i => a ⟨i.1, by
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega⟩)
      (t := (Finset.univ : Finset (Fin 4))) (H := by intro x hx; simp)
    rw [← hfib]
    norm_num
  rcases exists_two_of_sum_four cL jsp hcL_jsp hLsum with ⟨j, hj2⟩
  have hj_ne : j ≠ jsp := by
    intro h
    subst h
    exact absurd hj2 (by rw [hcL_jsp]; norm_num)
  have honj : ¬ onSp j := by
    intro h'
    dsimp only [onSp] at h'
    exact hj_ne h'.symm
  have hcS_j : cS j = 1 := by
    have h := hone j
    simp only [honj, if_false] at h
    omega
  have hcaseC : False := by
    have hcLmul : 2 * braunL k ≤ (cL j : ℝ) * braunL k := by
      have hcLcast : (2 : ℝ) ≤ (cL j : ℝ) := by exact_mod_cast hj2
      exact mul_le_mul_of_nonneg_right hcLcast (le_of_lt (braunL_pos k))
    have hcSmul : (cS j : ℝ) * braunS k = braunS k := by
      have hcSc : (cS j : ℝ) = 1 := by exact_mod_cast hcS_j
      rw [hcSc, one_mul]
    have hge : braunSp k + braunL k ≤ (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k := by
      nlinarith [hcLmul, hcSmul, braun_S_twoL_ge_bound k hk]
    have hlt : (cL j : ℝ) * braunL k + (cS j : ℝ) * braunS k < braunSp k + braunL k := by
      have h := hload_lt j
      rw [hload j] at h
      simpa [honj, if_false] using h
    nlinarith
  exact hcaseC

set_option linter.constructorNameAsVariable false in
/-- Table 6: OPT of the prefix through S⁺_k equals S⁺_k + L_k (k ≥ 1). -/
theorem braun_opt_prefix_Sp (k : ℕ) (hk : 1 ≤ k) :
    optMakespan (m := 4) (braunPrefixSp k) = braunSp k + braunL k := by
  apply le_antisymm
  · exact braun_opt_prefix_Sp_le k hk
  · rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
    have hblock : braunSp (k' + 1) + braunL (k' + 1) ≤
        optMakespan (m := 4) (braunLayerBlock (k' + 1)) := by
      apply Finset.le_inf'
      intro a ha
      exact braunLayerBlock_makespan_ge (k' + 1) (by omega) a
    have hsuffix : optMakespan (m := 4) (braunLayerBlock (k' + 1)) ≤
        optMakespan (m := 4) (braunPrefixSp (k' + 1)) := by
      dsimp only [braunPrefixSp]
      exact optMakespan_suffix_ge (braunPrefixSp k') (braunLayerBlock (k' + 1)) (braunPrefixSp_nonneg k')
    exact le_trans hblock hsuffix

/-! ### Theorem 1: the adaptive adversary (forcing induction) -/

/-- √3 ≤ 2. -/
lemma braun_sqrt3_le_two : Real.sqrt 3 ≤ 2 := by
  have h := sq_le_sq.mp (show Real.sqrt 3 ^ 2 ≤ (2 : ℝ) ^ 2 by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num)
  rwa [abs_of_nonneg (Real.sqrt_nonneg 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h

/-- α ≤ 3. -/
lemma braunα_le_three : braunα ≤ 3 := by
  dsimp [braunα]
  linarith [braun_sqrt3_le_two]

/-- Trap after L₀: two L₀ jobs on one machine beat the bound (witness OPT = L₀). -/
lemma braun_trap_L0 :
    Real.sqrt 3 * braunL 0 - (2 - Real.sqrt 3) ≤ 2 * braunL 0 := by
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  rw [braun_two_sub_sqrt3, hs3]
  dsimp [braunL]
  ring_nf
  nlinarith [braunα_le_three]

/-- Trap after S₀: two S₀ jobs on one machine beat the bound (witness OPT = L₀ + S₀). -/
lemma braun_trap_S0 :
    Real.sqrt 3 * (braunL 0 + braunS 0) - (2 - Real.sqrt 3) ≤ braunL 0 + 2 * braunS 0 := by
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  rw [braun_two_sub_sqrt3, hs3]
  dsimp [braunS, braunL]
  ring_nf
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  nlinarith [hα2, braunα_le_three]

/-- Trap after L₁: two L₁ jobs on one machine beat the bound (witness OPT = Φ₀ + L₁). -/
lemma braun_trap_L1 :
    Real.sqrt 3 * (braunSumLS 0 + braunL 1) - (2 - Real.sqrt 3) ≤ braunSumLS 0 + 2 * braunL 1 := by
  have hsum0 : braunSumLS 0 = braunL 0 + braunS 0 := by simp [braunSumLS]
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  rw [hsum0, braun_two_sub_sqrt3, hs3]
  dsimp [braunS, braunL, braunQ]
  ring_nf
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
    calc
      braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
      _ = braunα * (2 * braunα + 2) := by rw [hα2]
      _ = 2 * braunα ^ 2 + 2 * braunα := by ring
      _ = 6 * braunα + 4 := by rw [hα2]; ring
  nlinarith [hα2, hα3, braunα_le_three]

/-- Trap after S₁: two S₁ jobs on one machine beat the bound (witness OPT = S₁ + L₁). -/
lemma braun_trap_S1 :
    Real.sqrt 3 * (braunS 1 + braunL 1) - (2 - Real.sqrt 3) ≤ braunSumLS 0 + braunL 1 + 2 * braunS 1 := by
  have hsum0 : braunSumLS 0 = braunL 0 + braunS 0 := by simp [braunSumLS]
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  rw [hsum0, braun_two_sub_sqrt3, hs3]
  dsimp [braunS, braunL, braunQ]
  ring_nf
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
    calc
      braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
      _ = braunα * (2 * braunα + 2) := by rw [hα2]
      _ = 2 * braunα ^ 2 + 2 * braunα := by ring
      _ = 6 * braunα + 4 := by rw [hα2]; ring
  have hα4 : braunα ^ 4 = 16 * braunα + 12 := by
    calc
      braunα ^ 4 = braunα * braunα ^ 3 := by rw [pow_succ']
      _ = braunα * (6 * braunα + 4) := by rw [hα3]
      _ = 6 * braunα ^ 2 + 4 * braunα := by ring
      _ = 16 * braunα + 12 := by rw [hα2]; ring
  nlinarith [hα2, hα3, hα4]

/-- OPT of the L₀-trap witness (four L₀ jobs) equals L₀. -/
lemma braun_opt_replicate4_L0 :
    optMakespan (m := 4) (List.replicate 4 (braunL 0)) = braunL 0 := by
  apply le_antisymm
  · have hle := optMakespan_le_of_schedule (m := 4) (List.replicate 4 (braunL 0))
      (fun _ : Fin 4 => braunL 0) (diagAssignReplicate (m := 4) (braunL 0)) (by
        rw [scheduleLoads_replicate_diag (m := 4) (braunL 0)])
    rwa [makespan_const (m := 4)] at hle
  · have hge := optMakespan_ge_max_job (m := 4) (List.replicate 4 (braunL 0)) (by
      intro p hp
      rcases List.mem_replicate.mp hp with ⟨_, heq⟩
      rw [heq]
      exact le_of_lt (braunL_pos 0))
    have hmax : maxJobSize (List.replicate 4 (braunL 0)) = braunL 0 := by
      dsimp only [maxJobSize]
      have h0 : 0 ≤ braunL 0 := le_of_lt (braunL_pos 0)
      simp [h0]
    rwa [hmax] at hge

/-- OPT of the base prefix (L₀×4 ++ S₀×4) equals L₀ + S₀ = Φ₀. -/
lemma braun_opt_prefix0 :
    optMakespan (m := 4) (braunPrefixSp 0) = braunL 0 + braunS 0 := by
  apply le_antisymm
  · have hle := optMakespan_le_of_schedule (m := 4) (braunPrefixSp 0)
      (fun _ : Fin 4 => braunL 0 + braunS 0)
      (appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0))
        (diagAssignReplicate (m := 4) (braunL 0)) (diagAssignReplicate (m := 4) (braunS 0))) (by
          dsimp only [braunPrefixSp]
          ext j
          rw [scheduleLoads_append (m := 4),
            scheduleLoads_replicate_diag (m := 4) (braunL 0),
            scheduleLoads_replicate_diag (m := 4) (braunS 0)])
    rwa [makespan_const (m := 4)] at hle
  · have hge := optMakespan_ge_avg (m := 4) (braunPrefixSp 0)
    have htot : totalLoad (braunPrefixSp 0) / ((4 : ℕ) : ℝ) = braunL 0 + braunS 0 := by
      dsimp only [braunPrefixSp, totalLoad]
      rw [List.sum_append]
      simp only [List.sum_replicate, nsmul_eq_mul]
      nlinarith
    rwa [htot] at hge

/-- OPT of the L₁-trap witness (base ++ four L₁ jobs) is at most Φ₀ + L₁. -/
lemma braun_opt_prefix_4L1_le :
    optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) ≤ braunSumLS 0 + braunL 1 := by
  have hle := optMakespan_le_of_schedule (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1))
    (fun _ : Fin 4 => braunSumLS 0 + braunL 1)
    (appendAssign (m := 4) (braunPrefixSp 0) (List.replicate 4 (braunL 1))
      (appendAssign (m := 4) (List.replicate 4 (braunL 0)) (List.replicate 4 (braunS 0))
        (diagAssignReplicate (m := 4) (braunL 0)) (diagAssignReplicate (m := 4) (braunS 0)))
      (diagAssignReplicate (m := 4) (braunL 1))) (by
        dsimp only [braunPrefixSp]
        ext j
        rw [scheduleLoads_append (m := 4), scheduleLoads_append (m := 4),
          scheduleLoads_replicate_diag (m := 4) (braunL 0),
          scheduleLoads_replicate_diag (m := 4) (braunS 0),
          scheduleLoads_replicate_diag (m := 4) (braunL 1)]
        simp [braunSumLS])
  rwa [makespan_const (m := 4)] at hle

/-- Length of the S₁-trap witness sequence. -/
lemma braun_W3_length :
    (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)).length = 15 := by
  rw [List.length_append, List.length_append, braunPrefixSp_length]
  norm_num

/-- S₁-trap witness packing: three machines take {S₁, L₁}; the fourth machine
    takes {L₁, L₀×4, S₀×4}. -/
def braunAssign3S1 :
    Fin (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)).length → Fin 4 :=
  fun i =>
    if i.1 < 8 then 3
    else if i.1 = 8 then 0
    else if i.1 = 9 then 1
    else if i.1 = 10 then 2
    else if i.1 = 11 then 3
    else if i.1 = 12 then 0
    else if i.1 = 13 then 1
    else 2

/-- Restriction of `braunAssign3S1` to the base prefix (all → machine 3). -/
def braunAssign3S1_P0part : Fin (braunPrefixSp 0).length → Fin 4 :=
  fun i => braunAssign3S1 ⟨i.1, by
    have h8 : (braunPrefixSp 0).length = 8 := braunPrefixSp_length 0
    rw [braun_W3_length]
    omega⟩

/-- Restriction of `braunAssign3S1` to the four L₁ jobs (positions 8–11). -/
def braunAssign3S1_Lpart : Fin 4 → Fin 4 :=
  fun i => braunAssign3S1 ⟨8 + i.1, by
    have h4 : (List.replicate 4 (braunL 1)).length = 4 := by simp only [List.length_replicate]
    rw [braun_W3_length]
    omega⟩

/-- Restriction of `braunAssign3S1` to the three S₁ jobs (positions 12–14). -/
def braunAssign3S1_Spart : Fin 3 → Fin 4 :=
  fun i => braunAssign3S1 ⟨12 + i.1, by
    have h3 : (List.replicate 3 (braunS 1)).length = 3 := by simp only [List.length_replicate]
    rw [braun_W3_length]
    omega⟩

/-- Loads of the S₁-trap witness packing. -/
lemma braunAssign3S1_loads :
    scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 0 = braunL 1 + braunS 1 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 1 = braunL 1 + braunS 1 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 2 = braunL 1 + braunS 1 ∧
    scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 3 = 4 * braunL 0 + 4 * braunS 0 + braunL 1 := by
  have hsplit (j : Fin 4) :
      scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 j =
        scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part j +
        scheduleLoads (m := 4) (List.replicate 4 (braunL 1)) braunAssign3S1_Lpart j +
        scheduleLoads (m := 4) (List.replicate 3 (braunS 1)) braunAssign3S1_Spart j := by
    have h1 := scheduleLoads_split_append (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) (List.replicate 3 (braunS 1)) braunAssign3S1 j
    have h2 := scheduleLoads_split_append (braunPrefixSp 0) (List.replicate 4 (braunL 1))
      (fun i : Fin (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)).length => braunAssign3S1 ⟨i.1, by
        have h12 : (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)).length = 12 := by
          rw [List.length_append, braunPrefixSp_length, List.length_replicate]
        rw [braun_W3_length]
        omega⟩) j
    rw [h1, h2]
    rfl
  have hP0zero (j : Fin 4) (hj : j ≠ 3) :
      scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part j = 0 := by
    apply scheduleLoads_zero_of_forall_ne
    intro i
    dsimp only [braunAssign3S1_P0part, braunAssign3S1]
    have hi8 : i.1 < 8 := by
      have h8 : (braunPrefixSp 0).length = 8 := braunPrefixSp_length 0
      omega
    simp [hi8]
    exact fun h => hj h.symm
  have hP0three :
      scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part 3 = 4 * braunL 0 + 4 * braunS 0 := by
    have hzero0 : scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part 0 = 0 := hP0zero 0 (by decide)
    have hzero1 : scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part 1 = 0 := hP0zero 1 (by decide)
    have hzero2 : scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part 2 = 0 := hP0zero 2 (by decide)
    have hsum := sum_scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part
    have h3 := fin4_sum_extract3 (fun j' => scheduleLoads (m := 4) (braunPrefixSp 0) braunAssign3S1_P0part j')
    rw [h3, hsum, hzero0, hzero1, hzero2]
    dsimp only [braunPrefixSp, totalLoad]
    rw [List.sum_append]
    simp [List.sum_replicate]
    ring
  have hcL0 : ((Finset.univ : Finset (Fin 4)).filter (fun i => braunAssign3S1_Lpart i = (0 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Lpart, braunAssign3S1]
    native_decide
  have hcL1 : ((Finset.univ : Finset (Fin 4)).filter (fun i => braunAssign3S1_Lpart i = (1 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Lpart, braunAssign3S1]
    native_decide
  have hcL2 : ((Finset.univ : Finset (Fin 4)).filter (fun i => braunAssign3S1_Lpart i = (2 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Lpart, braunAssign3S1]
    native_decide
  have hcL3 : ((Finset.univ : Finset (Fin 4)).filter (fun i => braunAssign3S1_Lpart i = (3 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Lpart, braunAssign3S1]
    native_decide
  have hcS0 : ((Finset.univ : Finset (Fin 3)).filter (fun i => braunAssign3S1_Spart i = (0 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Spart, braunAssign3S1]
    native_decide
  have hcS1 : ((Finset.univ : Finset (Fin 3)).filter (fun i => braunAssign3S1_Spart i = (1 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Spart, braunAssign3S1]
    native_decide
  have hcS2 : ((Finset.univ : Finset (Fin 3)).filter (fun i => braunAssign3S1_Spart i = (2 : Fin 4))).card = 1 := by
    dsimp only [braunAssign3S1_Spart, braunAssign3S1]
    native_decide
  have hcS3 : ((Finset.univ : Finset (Fin 3)).filter (fun i => braunAssign3S1_Spart i = (3 : Fin 4))).card = 0 := by
    dsimp only [braunAssign3S1_Spart, braunAssign3S1]
    native_decide
  constructor
  · rw [hsplit 0, hP0zero 0 (by decide),
      scheduleLoads_replicate4_eq_count (braunL 1) braunAssign3S1_Lpart 0,
      scheduleLoads_replicate3_eq_count (braunS 1) braunAssign3S1_Spart 0, hcL0, hcS0]
    ring
  constructor
  · rw [hsplit 1, hP0zero 1 (by decide),
      scheduleLoads_replicate4_eq_count (braunL 1) braunAssign3S1_Lpart 1,
      scheduleLoads_replicate3_eq_count (braunS 1) braunAssign3S1_Spart 1, hcL1, hcS1]
    ring
  constructor
  · rw [hsplit 2, hP0zero 2 (by decide),
      scheduleLoads_replicate4_eq_count (braunL 1) braunAssign3S1_Lpart 2,
      scheduleLoads_replicate3_eq_count (braunS 1) braunAssign3S1_Spart 2, hcL2, hcS2]
    ring
  · rw [hsplit 3, hP0three,
      scheduleLoads_replicate4_eq_count (braunL 1) braunAssign3S1_Lpart 3,
      scheduleLoads_replicate3_eq_count (braunS 1) braunAssign3S1_Spart 3, hcL3, hcS3]
    ring

/-- OPT of the S₁-trap witness is at most S₁ + L₁. -/
lemma braun_opt_prefix_3S1_le :
    optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) ≤ braunS 1 + braunL 1 := by
  have hle := optMakespan_le_of_schedule (m := 4)
    (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1))
    (scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1)
    braunAssign3S1 rfl
  refine le_trans hle ?_
  dsimp only [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  rcases braunAssign3S1_loads with ⟨h0, h1, h2, h3⟩
  fin_cases j
  · change scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 0 ≤ braunS 1 + braunL 1
    rw [h0]
    nlinarith
  · change scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 1 ≤ braunS 1 + braunL 1
    rw [h1]
    nlinarith
  · change scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 2 ≤ braunS 1 + braunL 1
    rw [h2]
    nlinarith
  · change scheduleLoads (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) braunAssign3S1 3 ≤ braunS 1 + braunL 1
    rw [h3]
    have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
    have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
      calc
        braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
        _ = braunα * (2 * braunα + 2) := by rw [hα2]
        _ = 2 * braunα ^ 2 + 2 * braunα := by ring
        _ = 6 * braunα + 4 := by rw [hα2]; ring
    dsimp only [braunS, braunL, braunQ]
    nlinarith [hα2, hα3, braunα_pos]

/-- Three identical jobs of size `x` on a uniform base load force either an
    imbalanced makespan ≥ base + 2x, or three distinct machines at base + x
    and one machine untouched at base. -/
lemma braun_three_from_base (alg : OnlineAlgorithm 4) (base x : ℝ) (hxpos : 0 < x)
    (loads_before : Loads 4) (h_uniform : ∀ i : Fin 4, loads_before i = base) :
    let loads_after := (List.replicate 3 x).foldl (step (m := 4) alg) loads_before
    makespan 4 loads_after ≥ base + 2 * x ∨
    (∃ j0 : Fin 4, loads_after j0 = base ∧ ∀ i : Fin 4, i ≠ j0 → loads_after i = base + x) := by
  intro loads_after
  have h_total_after : (∑ i : Fin 4, loads_after i) = (4 : ℝ) * base + 3 * x := by
    rw [show loads_after = (List.replicate 3 x).foldl (step (m := 4) alg) loads_before from rfl]
    rw [sum_foldl_step (m := 4) alg loads_before (List.replicate 3 x)]
    have h_sum_before : (∑ i : Fin 4, loads_before i) = (4 : ℝ) * base := by simp [h_uniform]
    rw [h_sum_before]
    simp [totalLoad]
    ring
  choose n hn using braun_loads_multiples_from_base alg base x 3 loads_before
    (by intro i; rw [h_uniform i]; exact ⟨0, by simp⟩)
  have h_sum_n : (∑ i : Fin 4, n i) = 3 := by
    have h_all : (∑ i : Fin 4, (base + (n i : ℝ) * x)) = (4 : ℝ) * base + 3 * x := by
      calc
        (∑ i : Fin 4, (base + (n i : ℝ) * x)) = (∑ i : Fin 4, loads_after i) := by
          apply Finset.sum_congr rfl
          intro i hi
          change base + (n i : ℝ) * x =
            ((List.replicate 3 x).foldl (step (m := 4) alg) loads_before) i
          exact (hn i).symm
        _ = (4 : ℝ) * base + 3 * x := h_total_after
    have h_expand : (∑ i : Fin 4, (base + (n i : ℝ) * x)) =
        (4 : ℝ) * base + (∑ i : Fin 4, (n i : ℝ) * x) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand] at h_all
    have h_sum_n_real : (∑ i : Fin 4, ((n i : ℕ) : ℝ)) = (3 : ℝ) := by
      have h' : (∑ i : Fin 4, ((n i : ℕ) : ℝ)) * x = (3 : ℝ) * x := by
        have hsum : (∑ i : Fin 4, ((n i : ℕ) : ℝ) * x) = (∑ i : Fin 4, ((n i : ℕ) : ℝ)) * x := by
          rw [← Finset.sum_mul]
        nlinarith [h_all, hsum]
      exact mul_right_cancel₀ (ne_of_gt hxpos) h'
    exact_mod_cast h_sum_n_real
  by_cases h_exists : ∃ i, 2 ≤ n i
  · left
    rcases h_exists with ⟨i, hi⟩
    have h_load_ge : base + 2 * x ≤ loads_after i := by
      rw [show loads_after = (List.replicate 3 x).foldl (step (m := 4) alg) loads_before from rfl]
      rw [hn i]
      have : (2 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hi
      nlinarith [this, le_of_lt hxpos]
    have h_makespan_ge : base + 2 * x ≤ makespan 4 loads_after := by
      have h := makespan_ge_each (m := 4) loads_after i
      linarith
    exact h_makespan_ge
  · right
    push_neg at h_exists
    have hn_le_one : ∀ i, n i ≤ 1 := by intro i; have h := h_exists i; omega
    have h_exists0 : ∃ j0 : Fin 4, n j0 = 0 := by
      by_contra hnone
      have hall : ∀ j : Fin 4, 1 ≤ n j := by
        intro j
        by_contra hj
        exact hnone ⟨j, by omega⟩
      rw [Fin.sum_univ_four] at h_sum_n
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      have h3 := hall 3
      omega
    rcases h_exists0 with ⟨j0, hj0⟩
    refine ⟨j0, ?_, ?_⟩
    · rw [show loads_after = (List.replicate 3 x).foldl (step (m := 4) alg) loads_before from rfl]
      rw [hn j0, hj0]
      norm_num
    · intro i hi
      have hn_i : n i = 1 := by
        have hle_i : n i ≤ 1 := hn_le_one i
        have hge_i : 1 ≤ n i := by
          have hbound : ∀ k : Fin 4, n k ≤ (if k = j0 then n j0 else if k = i then n i else 1) := by
            intro k
            by_cases hk0 : k = j0
            · rw [if_pos hk0, hk0]
            · by_cases hki : k = i
              · rw [if_neg hk0, if_pos hki, hki]
              · rw [if_neg hk0, if_neg hki]
                exact hn_le_one k
          have hle : (∑ k : Fin 4, n k) ≤ (∑ k : Fin 4, (if k = j0 then n j0 else if k = i then n i else 1)) :=
            Finset.sum_le_sum (fun k hk => hbound k)
          have hsum_eval : (∑ k : Fin 4, (if k = j0 then n j0 else if k = i then n i else 1)) = n j0 + n i + 2 := by
            have hneq : j0 ≠ i := fun h => hi h.symm
            rw [Fin.sum_univ_four]
            fin_cases j0 <;> fin_cases i <;> simp [hneq] at * <;> omega
          omega
        omega
      rw [show loads_after = (List.replicate 3 x).foldl (step (m := 4) alg) loads_before from rfl]
      rw [hn i, hn_i]
      norm_num

/-! ### Prefix certificates: every adversary witness is a prefix of the family -/

/-- Reflexivity of `List.IsPrefix` (used to avoid API-version differences). -/
lemma braun_isPrefix_refl (σ : JobSequence) : List.IsPrefix σ σ := ⟨[], by simp⟩

/-- Transitivity of `List.IsPrefix` (used to avoid API-version differences). -/
lemma braun_isPrefix_trans {σ τ ρ : JobSequence} (h1 : List.IsPrefix σ τ) (h2 : List.IsPrefix τ ρ) :
    List.IsPrefix σ ρ := by
  rcases h1 with ⟨t1, rfl⟩
  rcases h2 with ⟨t2, rfl⟩
  refine ⟨t1 ++ t2, ?_⟩
  rw [List.append_assoc]

/-- The initial L₀ layer is a prefix of `braunPrefixSp 0`. -/
lemma braun_L0_prefix_pref0 :
    List.IsPrefix (List.replicate 4 (braunL 0)) (braunPrefixSp 0) := by
  refine ⟨List.replicate 4 (braunS 0), ?_⟩
  rfl

/-- Each step of the prefix recursion extends by one layer block. -/
lemma braun_prefix_step (k : ℕ) : List.IsPrefix (braunPrefixSp k) (braunPrefixSp (k + 1)) := by
  refine ⟨braunLayerBlock (k + 1), ?_⟩
  rfl

/-- `braunPrefixSp k` is a prefix of `braunPrefixSp r` for k ≤ r. -/
lemma braun_prefix_mono {k r : ℕ} (h : k ≤ r) :
    List.IsPrefix (braunPrefixSp k) (braunPrefixSp r) := by
  induction h with
  | refl => exact braun_isPrefix_refl (braunPrefixSp k)
  | step h ih => exact braun_isPrefix_trans ih (braun_prefix_step _)

/-- The L_k-trap witness (prefix through S⁺_{k-1} plus the L_k layer) is a
    prefix of `braunPrefixSp k` (k ≥ 1). -/
lemma braun_L_witness_prefix (k : ℕ) (hk : 1 ≤ k) :
    List.IsPrefix (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k)) (braunPrefixSp k) := by
  refine ⟨List.replicate 3 (braunS k) ++ [braunSp k], ?_⟩
  have hk' : k = (k - 1) + 1 := by omega
  conv_rhs => rw [hk']
  dsimp only [braunPrefixSp, braunLayerBlock]
  rw [← hk']
  rw [List.append_assoc, List.append_assoc]

/-- The S_k-trap witness (prefix plus L_k×4 and S_k×3) is a prefix of
    `braunPrefixSp k` (k ≥ 1). -/
lemma braun_S_witness_prefix (k : ℕ) (hk : 1 ≤ k) :
    List.IsPrefix (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k))
      (braunPrefixSp k) := by
  refine ⟨[braunSp k], ?_⟩
  have hk' : k = (k - 1) + 1 := by omega
  conv_rhs => rw [hk']
  dsimp only [braunPrefixSp, braunLayerBlock]
  rw [← hk']
  rw [List.append_assoc, List.append_assoc, List.append_assoc]

/-- `braunPrefixSp r` is a prefix of the full sequence σ_r. -/
lemma braun_prefix_seq (r : ℕ) : List.IsPrefix (braunPrefixSp r) (braunSeq r) := by
  refine ⟨[braunF r], ?_⟩
  rw [braunPrefixSp_eq_flat r, List.append_assoc, List.append_assoc]
  dsimp only [braunSeq]
  rw [List.append_assoc, List.append_assoc]

/-! ### Base forcing (with prefix certificates) -/

/-- Base forcing: the L₀/S₀ layers either yield a witness achieving the bound
    (a prefix of `braunPrefixSp 0`), or leave every machine at load Φ₀ after
    `braunPrefixSp 0`. -/
lemma braun_base_forcing_pref (alg : OnlineAlgorithm 4) :
    (∃ σ : JobSequence, List.IsPrefix σ (braunPrefixSp 0) ∧
       Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, runAlgorithm 4 alg (braunPrefixSp 0) i = braunSumLS 0) := by
  rcases braun_layer_separation_from_base alg 0 (braunL 0) (braunL_pos 0)
      (fun _ : Fin 4 => (0 : ℝ)) (by intro i; rfl) with hbad | hgood
  · left
    refine ⟨List.replicate 4 (braunL 0), braun_L0_prefix_pref0, ?_⟩
    have hmk : 2 * braunL 0 ≤ algorithmMakespan 4 alg (List.replicate 4 (braunL 0)) := by
      dsimp only [algorithmMakespan, runAlgorithm]
      simpa using hbad
    calc
      Real.sqrt 3 * optMakespan (m := 4) (List.replicate 4 (braunL 0)) - (2 - Real.sqrt 3)
          = Real.sqrt 3 * braunL 0 - (2 - Real.sqrt 3) := by rw [braun_opt_replicate4_L0]
      _ ≤ 2 * braunL 0 := braun_trap_L0
      _ ≤ algorithmMakespan 4 alg (List.replicate 4 (braunL 0)) := hmk
  · have hgood' : ∀ i : Fin 4, runAlgorithm 4 alg (List.replicate 4 (braunL 0)) i = braunL 0 := by
      intro i
      dsimp only [runAlgorithm]
      simpa using hgood i
    rcases braun_layer_separation_from_base alg (braunL 0) (braunS 0) (braunS_pos 0)
        (runAlgorithm 4 alg (List.replicate 4 (braunL 0))) hgood' with hbad2 | hgood2
    · left
      refine ⟨braunPrefixSp 0, braun_isPrefix_refl (braunPrefixSp 0), ?_⟩
      have hmk : braunL 0 + 2 * braunS 0 ≤ algorithmMakespan 4 alg (braunPrefixSp 0) := by
        dsimp only [algorithmMakespan, runAlgorithm, braunPrefixSp]
        rw [List.foldl_append]
        exact hbad2
      calc
        Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 0) - (2 - Real.sqrt 3)
            = Real.sqrt 3 * (braunL 0 + braunS 0) - (2 - Real.sqrt 3) := by rw [braun_opt_prefix0]
        _ ≤ braunL 0 + 2 * braunS 0 := braun_trap_S0
        _ ≤ algorithmMakespan 4 alg (braunPrefixSp 0) := hmk
    · right
      intro i
      have hrun : runAlgorithm 4 alg (braunPrefixSp 0) i =
          ((List.replicate 4 (braunS 0)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (List.replicate 4 (braunL 0)))) i := by
        dsimp only [runAlgorithm, braunPrefixSp]
        rw [List.foldl_append]
      rw [hrun, hgood2 i]
      simp [braunSumLS]

/-- Base forcing without the prefix certificate. -/
lemma braun_base_forcing (alg : OnlineAlgorithm 4) :
    (∃ σ : JobSequence,
       Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, runAlgorithm 4 alg (braunPrefixSp 0) i = braunSumLS 0) := by
  rcases braun_base_forcing_pref alg with h | h
  · rcases h with ⟨σ, hpref, hb⟩
    exact Or.inl ⟨σ, hb⟩
  · exact Or.inr h

/-- Layer-1 forcing: from the balanced state Φ₀ after `braunPrefixSp 0`, the block
    {L₁×4, S₁×3, S⁺₁} either yields a witness achieving the bound, or leaves every
    machine at load ≥ Φ₁ after `braunPrefixSp 1`. -/
lemma braun_layer1_forcing_pref (alg : OnlineAlgorithm 4)
    (h0 : ∀ i : Fin 4, runAlgorithm 4 alg (braunPrefixSp 0) i = braunSumLS 0) :
    (∃ σ : JobSequence, List.IsPrefix σ (braunPrefixSp 1) ∧
       Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, braunSumLS 1 ≤ runAlgorithm 4 alg (braunPrefixSp 1) i) := by
  rcases braun_layer_separation_from_base alg (braunSumLS 0) (braunL 1) (braunL_pos 1)
      (runAlgorithm 4 alg (braunPrefixSp 0)) h0 with hLbad | hLgood
  · left
    refine ⟨braunPrefixSp 0 ++ List.replicate 4 (braunL 1), braun_L_witness_prefix 1 (by norm_num : (1 : ℕ) ≤ 1), ?_⟩
    have hmk : braunSumLS 0 + 2 * braunL 1 ≤ algorithmMakespan 4 alg (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) := by
      dsimp only [algorithmMakespan, runAlgorithm]
      rw [List.foldl_append]
      exact hLbad
    have hopt : optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) ≤ braunSumLS 0 + braunL 1 :=
      braun_opt_prefix_4L1_le
    have hsq : Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) ≤
        Real.sqrt 3 * (braunSumLS 0 + braunL 1) :=
      mul_le_mul_of_nonneg_left hopt (le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))
    calc
      Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) - (2 - Real.sqrt 3)
          ≤ Real.sqrt 3 * (braunSumLS 0 + braunL 1) - (2 - Real.sqrt 3) := by linarith
      _ ≤ braunSumLS 0 + 2 * braunL 1 := braun_trap_L1
      _ ≤ algorithmMakespan 4 alg (braunPrefixSp 0 ++ List.replicate 4 (braunL 1)) := hmk
  · rcases braun_three_from_base alg (braunSumLS 0 + braunL 1) (braunS 1) (braunS_pos 1)
        ((List.replicate 4 (braunL 1)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (braunPrefixSp 0))) hLgood with hSbad | hSgood
    · left
      refine ⟨braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1),
        braun_S_witness_prefix 1 (by norm_num : (1 : ℕ) ≤ 1), ?_⟩
      have hmk : braunSumLS 0 + braunL 1 + 2 * braunS 1 ≤
          algorithmMakespan 4 alg (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) := by
        dsimp only [algorithmMakespan, runAlgorithm]
        rw [List.foldl_append, List.foldl_append]
        exact hSbad
      have hopt : optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) ≤ braunS 1 + braunL 1 :=
        braun_opt_prefix_3S1_le
      have hsq : Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) ≤
          Real.sqrt 3 * (braunS 1 + braunL 1) :=
        mul_le_mul_of_nonneg_left hopt (le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))
      calc
        Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) - (2 - Real.sqrt 3)
            ≤ Real.sqrt 3 * (braunS 1 + braunL 1) - (2 - Real.sqrt 3) := by linarith
        _ ≤ braunSumLS 0 + braunL 1 + 2 * braunS 1 := braun_trap_S1
        _ ≤ algorithmMakespan 4 alg (braunPrefixSp 0 ++ List.replicate 4 (braunL 1) ++ List.replicate 3 (braunS 1)) := hmk
    · rcases hSgood with ⟨j0, hj0base, hj0rest⟩
      let l2 : Loads 4 := (List.replicate 3 (braunS 1)).foldl (step (m := 4) alg)
        ((List.replicate 4 (braunL 1)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (braunPrefixSp 0)))
      have hj0base' : l2 j0 = braunSumLS 0 + braunL 1 := hj0base
      have hj0rest' : ∀ i : Fin 4, i ≠ j0 → l2 i = braunSumLS 0 + braunL 1 + braunS 1 := hj0rest
      by_cases hjj0 : alg l2 (braunSp 1) = j0
      · right
        intro i
        have hrun : runAlgorithm 4 alg (braunPrefixSp 1) i = step (m := 4) alg l2 (braunSp 1) i := by
          dsimp only [braunPrefixSp, braunLayerBlock, runAlgorithm, l2]
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hrun]
        by_cases hij0 : i = j0
        · -- i = j0: receives S⁺₁
          dsimp only [step]
          rw [if_pos (by rw [hij0]; exact hjj0.symm)]
          rw [hij0, hj0base']
          simp [braunSumLS, braunSp, braunS, braunL, Finset.sum_range_succ]
          nlinarith [show (0 : ℝ) ≤ 2 * braunα by nlinarith [braunα_pos]]
        · -- i ≠ j0: untouched
          dsimp only [step]
          rw [if_neg (by
            intro h
            have : i = j0 := by rw [h, hjj0]
            exact hij0 this)]
          rw [hj0rest' i hij0]
          simp [braunSumLS, Finset.sum_range_succ]
          nlinarith
      · -- S⁺₁ lands on a machine carrying S₁ — the exact trap
        left
        refine ⟨braunPrefixSp 1, braun_isPrefix_refl (braunPrefixSp 1), ?_⟩
        have hjj0' : alg l2 (braunSp 1) ≠ j0 := hjj0
        have hrunj : runAlgorithm 4 alg (braunPrefixSp 1) (alg l2 (braunSp 1)) = step (m := 4) alg l2 (braunSp 1) (alg l2 (braunSp 1)) := by
          dsimp only [braunPrefixSp, braunLayerBlock, runAlgorithm, l2]
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hloadj : braunSumLS 1 + braunSp 1 ≤ runAlgorithm 4 alg (braunPrefixSp 1) (alg l2 (braunSp 1)) := by
          rw [hrunj]
          dsimp only [step]
          rw [if_pos rfl]
          rw [hj0rest' (alg l2 (braunSp 1)) hjj0']
          simp [braunSumLS, Finset.sum_range_succ]
          nlinarith
        have hmk : braunSumLS 1 + braunSp 1 ≤ algorithmMakespan 4 alg (braunPrefixSp 1) := by
          dsimp only [algorithmMakespan]
          exact le_trans hloadj (makespan_ge_each (m := 4) (runAlgorithm 4 alg (braunPrefixSp 1)) (alg l2 (braunSp 1)))
        have hid := braun_prefix_additive_identity 1 (by norm_num : 1 ≤ 1)
        have hoptS := braun_opt_prefix_Sp 1 (by norm_num : 1 ≤ 1)
        calc
          Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp 1) - (2 - Real.sqrt 3)
              = Real.sqrt 3 * (braunSp 1 + braunL 1) - (2 - Real.sqrt 3) := by rw [hoptS]
          _ = braunSumLS 1 + braunSp 1 := by rw [hid]
          _ ≤ algorithmMakespan 4 alg (braunPrefixSp 1) := hmk

/-- Layer-1 forcing without the prefix certificate. -/
lemma braun_layer1_forcing (alg : OnlineAlgorithm 4)
    (h0 : ∀ i : Fin 4, runAlgorithm 4 alg (braunPrefixSp 0) i = braunSumLS 0) :
    (∃ σ : JobSequence,
       Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, braunSumLS 1 ≤ runAlgorithm 4 alg (braunPrefixSp 1) i) := by
  rcases braun_layer1_forcing_pref alg h0 with h | h
  · rcases h with ⟨σ, hpref, hb⟩
    exact Or.inl ⟨σ, hb⟩
  · exact Or.inr h

/-! ### Theorem 1, general r: the per-layer forced induction (Table 3) -/

/-- Placing job `p` on machine `i` (local copy; `AdvTree.place` is not imported).
    Additive form: keeps the contribution of every placement visible. -/
def braunPlace (loads : Loads 4) (p : ℝ) (i : Fin 4) : Loads 4 :=
  fun j => loads j + (if j = i then p else 0)

/-- Four placements in a row. -/
def braunPlace4 (loads : Loads 4) (x : ℝ) (m1 m2 m3 m4 : Fin 4) : Loads 4 :=
  braunPlace (braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3) x m4

/-- `step` is `braunPlace` at the algorithm's choice. -/
lemma step_eq_braunPlace (alg : OnlineAlgorithm 4) (loads : Loads 4) (x : ℝ) :
    step (m := 4) alg loads x = braunPlace loads x (alg loads x) := by
  ext i
  dsimp [step, braunPlace]
  by_cases h : i = alg loads x <;> simp [h]

/-- Four pairwise distinct machines exhaust Fin 4. -/
lemma braun_four_distinct_univ (m1 m2 m3 m4 : Fin 4)
    (hd : m1 ≠ m2 ∧ m1 ≠ m3 ∧ m1 ≠ m4 ∧ m2 ≠ m3 ∧ m2 ≠ m4 ∧ m3 ≠ m4) :
    ({m1, m2, m3, m4} : Finset (Fin 4)) = Finset.univ := by
  refine Finset.eq_univ_of_card (s := ({m1, m2, m3, m4} : Finset (Fin 4))) ?_
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton, Fintype.card_fin]
  · simp only [Finset.mem_singleton]
    exact hd.2.2.2.2.2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd.2.2.2.1, hd.2.2.2.2.1⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd.1, hd.2.1, hd.2.2.1⟩

/-- Placing four jobs on pairwise distinct machines gives each machine exactly
    one of them. -/
lemma braun_place4_loads_distinct (loads : Loads 4) (x : ℝ) (m1 m2 m3 m4 : Fin 4) (i : Fin 4)
    (hd : m1 ≠ m2 ∧ m1 ≠ m3 ∧ m1 ≠ m4 ∧ m2 ≠ m3 ∧ m2 ≠ m4 ∧ m3 ≠ m4) :
    braunPlace4 loads x m1 m2 m3 m4 i = loads i + x := by
  have huniv := braun_four_distinct_univ m1 m2 m3 m4 hd
  have hmem : i ∈ ({m1, m2, m3, m4} : Finset (Fin 4)) := by
    rw [huniv]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h3 | h4
  · dsimp [braunPlace4, braunPlace]
    rw [if_pos h1]
    rw [if_neg (show i ≠ m2 by intro h; exact hd.1 (h1.symm.trans h))]
    rw [if_neg (show i ≠ m3 by intro h; exact hd.2.1 (h1.symm.trans h))]
    rw [if_neg (show i ≠ m4 by intro h; exact hd.2.2.1 (h1.symm.trans h))]
    ring
  · dsimp [braunPlace4, braunPlace]
    rw [if_pos h2]
    rw [if_neg (show i ≠ m1 by intro h; exact hd.1 (h.symm.trans h2))]
    rw [if_neg (show i ≠ m3 by intro h; exact hd.2.2.2.1 (h2.symm.trans h))]
    rw [if_neg (show i ≠ m4 by intro h; exact hd.2.2.2.2.1 (h2.symm.trans h))]
    ring
  · dsimp [braunPlace4, braunPlace]
    rw [if_pos h3]
    rw [if_neg (show i ≠ m1 by intro h; exact hd.2.1 (h.symm.trans h3))]
    rw [if_neg (show i ≠ m2 by intro h; exact hd.2.2.2.1 (h.symm.trans h3))]
    rw [if_neg (show i ≠ m4 by intro h; exact hd.2.2.2.2.2 (h3.symm.trans h))]
    ring
  · dsimp [braunPlace4, braunPlace]
    rw [if_pos h4]
    rw [if_neg (show i ≠ m1 by intro h; exact hd.2.2.1 (h.symm.trans h4))]
    rw [if_neg (show i ≠ m2 by intro h; exact hd.2.2.2.2.1 (h.symm.trans h4))]
    rw [if_neg (show i ≠ m3 by intro h; exact hd.2.2.2.2.2 (h.symm.trans h4))]
    ring

/-- Four identical jobs on 4 machines: either some machine gets two and its
    load reaches `loads i + 2x`, or every machine gets exactly one. -/
lemma braun_place4_either (loads : Loads 4) (x : ℝ) (hxpos : 0 ≤ x)
    (m1 m2 m3 m4 : Fin 4) :
    (∀ i : Fin 4, braunPlace4 loads x m1 m2 m3 m4 i = loads i + x) ∨
    ∃ i : Fin 4, loads i + 2 * x ≤ braunPlace4 loads x m1 m2 m3 m4 i := by
  by_cases h12 : m1 = m2
  · right
    refine ⟨m1, ?_⟩
    dsimp [braunPlace4, braunPlace]
    rw [if_pos rfl, if_pos h12]
    split_ifs
    all_goals nlinarith
  · by_cases h13 : m1 = m3
    · right
      refine ⟨m1, ?_⟩
      dsimp [braunPlace4, braunPlace]
      rw [if_pos rfl, if_pos h13]
      split_ifs
      all_goals nlinarith
    · by_cases h14 : m1 = m4
      · right
        refine ⟨m1, ?_⟩
        dsimp [braunPlace4, braunPlace]
        rw [if_pos rfl, if_pos h14]
        split_ifs
        all_goals nlinarith
      · by_cases h23 : m2 = m3
        · right
          refine ⟨m2, ?_⟩
          dsimp [braunPlace4, braunPlace]
          rw [if_pos rfl, if_pos h23]
          split_ifs
          all_goals nlinarith
        · by_cases h24 : m2 = m4
          · right
            refine ⟨m2, ?_⟩
            dsimp [braunPlace4, braunPlace]
            rw [if_pos rfl, if_pos h24]
            split_ifs
            all_goals nlinarith
          · by_cases h34 : m3 = m4
            · right
              refine ⟨m3, ?_⟩
              dsimp [braunPlace4, braunPlace]
              rw [if_pos rfl, if_pos h34]
              split_ifs
              all_goals nlinarith
            · left
              intro i
              exact braun_place4_loads_distinct loads x m1 m2 m3 m4 i
                ⟨h12, h13, h14, h23, h24, h34⟩

/-- Three pairwise distinct machines leave one machine free. -/
lemma braun_three_distinct_exists_untouched (m1 m2 m3 : Fin 4)
    (h12 : m1 ≠ m2) (h13 : m1 ≠ m3) (h23 : m2 ≠ m3) :
    ∃ j0 : Fin 4, j0 ≠ m1 ∧ j0 ≠ m2 ∧ j0 ≠ m3 := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin 4)) ⊆ ({m1, m2, m3} : Finset (Fin 4)) := by
    intro j hj
    by_cases hj1 : j = m1
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hj1
    · by_cases hj2 : j = m2
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl hj2)
      · have hcases := h j
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inr (hcases hj1 hj2))
  have hcard := Finset.card_le_card hsub
  have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hcard3 : ({m1, m2, m3} : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact h23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
  rw [huniv, hcard3] at hcard
  norm_num at hcard

/-- Three placements on three pairwise distinct machines: the untouched machine
    keeps its load, the others gain exactly `x`. -/
lemma braun_place3_loads_distinct (loads : Loads 4) (x : ℝ) (m1 m2 m3 : Fin 4)
    (h12 : m1 ≠ m2) (h13 : m1 ≠ m3) (h23 : m2 ≠ m3) :
    ∃ j0 : Fin 4,
      braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 j0 = loads j0 ∧
      ∀ i : Fin 4, i ≠ j0 → braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 i = loads i + x := by
  rcases braun_three_distinct_exists_untouched m1 m2 m3 h12 h13 h23 with ⟨j0, hj01, hj02, hj03⟩
  have huniv : ({j0, m1, m2, m3} : Finset (Fin 4)) = Finset.univ := by
    refine Finset.eq_univ_of_card (s := ({j0, m1, m2, m3} : Finset (Fin 4))) ?_
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton, Fintype.card_fin]
    · simp only [Finset.mem_singleton]
      exact h23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hj01, hj02, hj03⟩
  refine ⟨j0, ?_, ?_⟩
  · dsimp [braunPlace]
    rw [if_neg hj01, if_neg hj02, if_neg hj03]
    ring
  · intro i hi
    have hi' : i ∈ ({j0, m1, m2, m3} : Finset (Fin 4)) := by
      rw [huniv]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with hij0 | hrest
    · exfalso
      exact hi hij0
    · dsimp [braunPlace]
      rcases hrest with h1 | h2 | h3
      · have hne2 : i ≠ m2 := by intro h; exact h12 (h1.symm.trans h)
        have hne3 : i ≠ m3 := by intro h; exact h13 (h1.symm.trans h)
        rw [if_pos h1, if_neg hne2, if_neg hne3]
        ring
      · have hne1 : i ≠ m1 := by intro h; exact h12 (h.symm.trans h2)
        have hne3 : i ≠ m3 := by intro h; exact h23 (h2.symm.trans h)
        rw [if_neg hne1, if_pos h2, if_neg hne3]
        ring
      · have hne1 : i ≠ m1 := by intro h; exact h13 (h.symm.trans h3)
        have hne2 : i ≠ m2 := by intro h; exact h23 (h.symm.trans h3)
        rw [if_neg hne1, if_neg hne2, if_pos h3]
        ring

/-- Four identical jobs of size `x` on top of loads bounded below by `base`:
    either the makespan reaches `base + 2x`, or every machine gains exactly
    one job. -/
lemma braun_layer_separation_lb (alg : OnlineAlgorithm 4) (base x : ℝ) (hxpos : 0 < x)
    (loads : Loads 4) (hlb : ∀ i : Fin 4, base ≤ loads i) :
    let loads_after := (List.replicate 4 x).foldl (step (m := 4) alg) loads
    makespan 4 loads_after ≥ base + 2 * x ∨
    (∀ i : Fin 4, loads_after i = loads i + x) := by
  intro loads_after
  let m1 : Fin 4 := alg loads x
  let m2 : Fin 4 := alg (step (m := 4) alg loads x) x
  let m3 : Fin 4 := alg (step (m := 4) alg (step (m := 4) alg loads x) x) x
  let m4 : Fin 4 := alg (step (m := 4) alg (step (m := 4) alg (step (m := 4) alg loads x) x) x) x
  have hfold : loads_after = braunPlace4 loads x m1 m2 m3 m4 := by
    dsimp only [loads_after, m1, m2, m3, m4, List.foldl, List.replicate]
    simp only [step_eq_braunPlace]
    dsimp only [braunPlace4]
  rcases braun_place4_either loads x (le_of_lt hxpos) m1 m2 m3 m4 with hall | htwo
  · right
    intro i
    rw [hfold]
    exact hall i
  · left
    rcases htwo with ⟨i, hi⟩
    have hge : base + 2 * x ≤ braunPlace4 loads x m1 m2 m3 m4 i := by
      nlinarith [hlb i, hi]
    rw [hfold]
    exact le_trans hge (makespan_ge_each (m := 4) (braunPlace4 loads x m1 m2 m3 m4) i)

/-- Three identical jobs of size `x` on top of loads bounded below by `base`:
    either some machine gets two and the makespan reaches `base + 2x`, or three
    distinct machines gain `x` and one machine is untouched. -/
lemma braun_three_from_lb (alg : OnlineAlgorithm 4) (base x : ℝ) (hxpos : 0 < x)
    (loads : Loads 4) (hlb : ∀ i : Fin 4, base ≤ loads i) :
    let loads_after := (List.replicate 3 x).foldl (step (m := 4) alg) loads
    makespan 4 loads_after ≥ base + 2 * x ∨
    (∃ j0 : Fin 4, loads_after j0 = loads j0 ∧ ∀ i : Fin 4, i ≠ j0 → loads_after i = loads i + x) := by
  intro loads_after
  let m1 : Fin 4 := alg loads x
  let m2 : Fin 4 := alg (step (m := 4) alg loads x) x
  let m3 : Fin 4 := alg (step (m := 4) alg (step (m := 4) alg loads x) x) x
  have hfold : loads_after = braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 := by
    dsimp only [loads_after, m1, m2, m3, List.foldl, List.replicate]
    simp only [step_eq_braunPlace]
  by_cases h12 : m1 = m2
  · left
    have hge : base + 2 * x ≤ braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 m1 := by
      dsimp [braunPlace]
      rw [if_pos rfl, if_pos h12]
      split_ifs
      all_goals nlinarith [hlb m1, hxpos]
    rw [hfold]
    exact le_trans hge (makespan_ge_each (m := 4) (braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3) m1)
  · by_cases h13 : m1 = m3
    · left
      have hge : base + 2 * x ≤ braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 m1 := by
        dsimp [braunPlace]
        rw [if_pos rfl, if_pos h13]
        split_ifs
        all_goals nlinarith [hlb m1, hxpos]
      rw [hfold]
      exact le_trans hge (makespan_ge_each (m := 4) (braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3) m1)
    · by_cases h23 : m2 = m3
      · left
        have hge : base + 2 * x ≤ braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3 m2 := by
          dsimp [braunPlace]
          rw [if_pos rfl, if_pos h23]
          split_ifs
          all_goals nlinarith [hlb m2, hxpos]
        rw [hfold]
        exact le_trans hge (makespan_ge_each (m := 4) (braunPlace (braunPlace (braunPlace loads x m1) x m2) x m3) m2)
      · right
        rcases braun_place3_loads_distinct loads x m1 m2 m3 h12 h13 h23 with ⟨j0, htouch, hothers⟩
        refine ⟨j0, ?_, ?_⟩
        · rw [hfold]
          exact htouch
        · intro i hi
          rw [hfold]
          exact hothers i hi

/-! ### The L_k and S_k trap inequalities (general k) -/

/-- α · (S⁺_{k−1} + L_{k−1} + L_k) = q^{k−1} · (15α + 11) (k ≥ 2). -/
lemma braun_SpL_pred_add_mul_alpha (k : ℕ) (hk : 2 ≤ k) :
    braunα * (braunSp (k - 1) + braunL (k - 1) + braunL k) =
      braunQ ^ (k - 1) * (15 * braunα + 11) := by
  have hk1 : 1 ≤ k - 1 := by omega
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
    calc
      braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
      _ = braunα * (2 * braunα + 2) := by rw [hα2]
      _ = 2 * braunα ^ 2 + 2 * braunα := by ring
      _ = 6 * braunα + 4 := by rw [hα2]; ring
  have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
    rw [pow_succ]
  rw [braunSp_closed (k - 1) hk1]
  dsimp only [braunL]
  rw [hqk]
  have hαinv : braunα * (braunα + 1 / braunα) = braunα ^ 2 + 1 := by
    field_simp [ne_of_gt braunα_pos]
  calc
    braunα * (braunQ ^ (k - 1) * (braunα + 1 / braunα) + braunQ ^ (k - 1) + braunQ ^ (k - 1) * braunQ)
        = braunQ ^ (k - 1) * (braunα * (braunα + 1 / braunα) + braunα + braunα * braunQ) := by ring
    _ = braunQ ^ (k - 1) * (braunα ^ 2 + 1 + braunα + braunα * braunQ) := by rw [hαinv]
    _ = braunQ ^ (k - 1) * (15 * braunα + 11) := by
          congr 1
          dsimp [braunQ]
          ring_nf
          nlinarith [hα2, hα3]

/-- The coefficient identity driving the L_k trap:
    (α−1)(15α+11) − α(3−α)q − 2αq = 3 − 2α. -/
lemma braun_trap_Lk_coef :
    (braunα - 1) * (15 * braunα + 11) - (3 - braunα) * braunα * braunQ - 2 * braunα * braunQ
      = 3 - 2 * braunα := by
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
    calc
      braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
      _ = braunα * (2 * braunα + 2) := by rw [hα2]
      _ = 2 * braunα ^ 2 + 2 * braunα := by ring
      _ = 6 * braunα + 4 := by rw [hα2]; ring
  have hα4 : braunα ^ 4 = 16 * braunα + 12 := by
    calc
      braunα ^ 4 = braunα * braunα ^ 3 := by rw [pow_succ']
      _ = braunα * (6 * braunα + 4) := by rw [hα3]
      _ = 6 * braunα ^ 2 + 4 * braunα := by ring
      _ = 16 * braunα + 12 := by rw [hα2]; ring
  dsimp [braunQ]
  ring_nf
  nlinarith [hα2, hα3, hα4]

/-- L_k trap (k ≥ 2): two L_k jobs on one machine beat the additive bound, with
    witness OPT ≤ S⁺_{k−1} + L_{k−1} + L_k. The proof reduces the difference to
    q^{k−1}·(3/α − 2) ≤ 0; the constant (3−2α)/α is negative since α > 2. -/
lemma braun_trap_Lk (k : ℕ) (hk : 2 ≤ k) :
    Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (2 - Real.sqrt 3)
      ≤ braunSumLS (k - 1) + 2 * braunL k := by
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
    rw [pow_succ]
  have hc0 : (1 + braunα) / (braunQ - 1) = 3 - braunα := by
    have h : (3 - braunα) * (braunQ - 1) = 1 + braunα := by
      dsimp [braunQ]
      nlinarith [braun_poly2]
    rw [← h]
    field_simp [braunQ_sub_one_ne_zero]
  have hquot : (1 + braunα) * ((braunQ ^ k - 1) / (braunQ - 1)) = (3 - braunα) * (braunQ ^ k - 1) := by
    calc
      (1 + braunα) * ((braunQ ^ k - 1) / (braunQ - 1))
          = (1 + braunα) * (braunQ ^ k - 1) / (braunQ - 1) := by ring
      _ = ((1 + braunα) / (braunQ - 1)) * (braunQ ^ k - 1) := by ring
      _ = (3 - braunα) * (braunQ ^ k - 1) := by rw [hc0]
  have hD : braunα * (Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (2 - Real.sqrt 3)
      - (braunSumLS (k - 1) + 2 * braunL k)) = braunQ ^ (k - 1) * (3 - 2 * braunα) := by
    rw [braun_two_sub_sqrt3, hs3, braunSumLS_eq, braun_geom_sum]
    rw [show (k - 1) + 1 = k by omega]
    rw [hquot]
    calc
      braunα * ((braunα - 1) * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (3 - braunα)
          - ((3 - braunα) * (braunQ ^ k - 1) + 2 * braunL k))
          = (braunα - 1) * (braunα * (braunSp (k - 1) + braunL (k - 1) + braunL k))
            - (3 - braunα) * braunα * braunQ ^ k - 2 * braunα * braunL k := by
              ring_nf
      _ = (braunα - 1) * (braunQ ^ (k - 1) * (15 * braunα + 11))
            - (3 - braunα) * braunα * (braunQ ^ (k - 1) * braunQ) - 2 * braunα * (braunQ ^ (k - 1) * braunQ) := by
              rw [braun_SpL_pred_add_mul_alpha k hk]
              dsimp only [braunL]
              rw [hqk]
      _ = braunQ ^ (k - 1) * ((braunα - 1) * (15 * braunα + 11) - (3 - braunα) * braunα * braunQ - 2 * braunα * braunQ) := by
              ring
      _ = braunQ ^ (k - 1) * (3 - 2 * braunα) := by rw [braun_trap_Lk_coef]
  have hnonpos : braunα * (Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (2 - Real.sqrt 3)
      - (braunSumLS (k - 1) + 2 * braunL k)) ≤ 0 := by
    rw [hD]
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt braunQ_pos) (k - 1))
      (by nlinarith [braunα_gt_two])
  have hαDle : braunα * (Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (2 - Real.sqrt 3)
      - (braunSumLS (k - 1) + 2 * braunL k)) ≤ braunα * 0 := by
    simpa using hnonpos
  have hle := le_of_mul_le_mul_left hαDle braunα_pos
  linarith

/-- S_k trap (k ≥ 1): two S_k jobs on one machine beat the additive bound, with
    witness OPT ≤ S_k + L_k. The identity (√3−2)S + √3·L = L collapses the
    claim to 0 ≤ Φ_{k−1} + (2−√3). -/
lemma braun_trap_Sk (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt 3 * (braunS k + braunL k) - (2 - Real.sqrt 3) ≤
      braunSumLS (k - 1) + braunL k + 2 * braunS k := by
  have hs3 : Real.sqrt 3 = braunα - 1 := by dsimp [braunα]; ring
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hid : (Real.sqrt 3 - 2) * braunS k + Real.sqrt 3 * braunL k = braunL k := by
    rw [hs3]
    dsimp [braunS, braunL]
    calc
      (braunα - 1 - 2) * (braunα * braunQ ^ k) + (braunα - 1) * braunQ ^ k
          = (braunα ^ 2 - 2 * braunα - 1) * braunQ ^ k := by ring
      _ = braunQ ^ k := by
            have hα2' : braunα ^ 2 - 2 * braunα - 1 = 1 := by nlinarith [hα2]
            rw [hα2']
            ring
  have hnonneg : 0 ≤ braunSumLS (k - 1) + (2 - Real.sqrt 3) := by
    apply add_nonneg
    · dsimp [braunSumLS]
      apply Finset.sum_nonneg
      intro i hi
      exact add_nonneg (le_of_lt (braunL_pos i)) (le_of_lt (braunS_pos i))
    · have hs3lt2 : Real.sqrt 3 < 2 := by
        have h : Real.sqrt 3 < Real.sqrt 4 :=
          Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) < 4)
        rwa [show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]] at h
      nlinarith
  calc
    Real.sqrt 3 * (braunS k + braunL k) - (2 - Real.sqrt 3)
        = braunL k + 2 * braunS k - (2 - Real.sqrt 3) := by nlinarith [hid]
    _ ≤ braunSumLS (k - 1) + braunL k + 2 * braunS k := by nlinarith [hnonneg]

/-! ### OPT witness bounds for the general-k traps -/

/-- The L_k-trap witness sequence: prefix through S⁺_{k−1}, then L_k×4. -/
def braunLkTrapWitness (k : ℕ) : JobSequence :=
  braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k)

/-- The S_k-trap witness sequence: prefix through S⁺_{k−1}, then L_k×4, S_k×3. -/
def braunSkTrapWitness (k : ℕ) : JobSequence :=
  braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k) ++ List.replicate 3 (braunS k)

/-- Assignment of the L_k-trap witness: the Table-6 packing of the prefix plus
    one L_k on each machine. -/
noncomputable def braunLkTrapAssign (k : ℕ) :
    Fin (braunLkTrapWitness k).length → Fin 4 :=
  appendAssign (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
    (braunPrefixAssign (k - 1)) (diagAssignReplicate (m := 4) (braunL k))

/-- OPT of the L_k-trap witness is at most S⁺_{k−1} + L_{k−1} + L_k (k ≥ 2). -/
lemma braun_opt_Lk_trap_le (k : ℕ) (hk : 2 ≤ k) :
    optMakespan (m := 4) (braunLkTrapWitness k) ≤ braunSp (k - 1) + braunL (k - 1) + braunL k := by
  have hk1 : 1 ≤ k - 1 := by omega
  have hle := optMakespan_le_of_schedule (m := 4) (braunLkTrapWitness k)
    (scheduleLoads (m := 4) (braunLkTrapWitness k) (braunLkTrapAssign k)) (braunLkTrapAssign k) rfl
  refine le_trans hle ?_
  dsimp only [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  have hdec (j : Fin 4) :
      scheduleLoads (m := 4) (braunLkTrapWitness k) (braunLkTrapAssign k) j =
        scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (braunPrefixAssign (k - 1)) j + braunL k := by
    dsimp only [braunLkTrapWitness, braunLkTrapAssign]
    rw [scheduleLoads_append (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
      (braunPrefixAssign (k - 1)) (diagAssignReplicate (m := 4) (braunL k)) j]
    rw [scheduleLoads_replicate_diag (m := 4) (braunL k)]
  rw [hdec j]
  have hpref : scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (braunPrefixAssign (k - 1)) j ≤
      braunSp (k - 1) + braunL (k - 1) :=
    le_trans (makespan_ge_each (m := 4) (scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (braunPrefixAssign (k - 1))) j)
      (braunPrefixAssign_makespan_le (k - 1) hk1)
  nlinarith

/-- Total load of the prefix through S⁺_{k−1} fits in a single S_k slot (k ≥ 1). -/
lemma braun_prefix_total_le_S (k : ℕ) (hk : 1 ≤ k) :
    totalLoad (braunPrefixSp (k - 1)) ≤ braunS k := by
  rw [braunPrefixSp_total (k - 1), braun_total_work (k - 1)]
  have hcpos : 0 < (4 + 6 * braunα) / (braunQ - 1) := by
    have hnum : 0 < 4 + 6 * braunα := by nlinarith [braunα_pos]
    have hden : 0 < braunQ - 1 := by linarith [braunQ_gt_one]
    positivity
  have hα2 : braunα ^ 2 = 2 * braunα + 2 := by nlinarith [braun_poly2]
  have hα3 : braunα ^ 3 = 6 * braunα + 4 := by
    calc
      braunα ^ 3 = braunα * braunα ^ 2 := by rw [pow_succ']
      _ = braunα * (2 * braunα + 2) := by rw [hα2]
      _ = 2 * braunα ^ 2 + 2 * braunα := by ring
      _ = 6 * braunα + 4 := by rw [hα2]; ring
  have h3F : 3 * braunF (k - 1) ≤ braunS k := by
    have hqk : braunQ ^ k = braunQ ^ (k - 1) * braunQ := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    have hcoef : 6 * braunα ≤ 2 * braunα ^ 3 := by nlinarith [hα3, braunα_pos]
    have hmul := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (le_of_lt braunQ_pos) (k - 1))
    dsimp [braunF, braunS, braunL]
    rw [hqk]
    dsimp [braunQ] at hmul ⊢
    nlinarith [hmul]
  nlinarith [h3F, hcpos]

/-- The S_k-trap assignment: the prefix goes to machine 3, the L_k layer
    diagonally, the three S_k jobs to machines 0, 1, 2. -/
noncomputable def braunSkTrapAssign (k : ℕ) :
    Fin (braunSkTrapWitness k).length → Fin 4 :=
  appendAssign (m := 4) (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k)) (List.replicate 3 (braunS k))
    (appendAssign (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
      (fun _ => 3) (diagAssignReplicate (m := 4) (braunL k)))
    (fun i : Fin 3 => ⟨i.1, by omega⟩)

/-- Loads of the S_k-trap assignment: machines 0–2 get L_k + S_k, machine 3
    gets the whole prefix plus one L_k. -/
lemma braunSkTrapAssign_loads (k : ℕ) :
    scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 0 = braunL k + braunS k ∧
    scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 1 = braunL k + braunS k ∧
    scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 2 = braunL k + braunS k ∧
    scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 3 = totalLoad (braunPrefixSp (k - 1)) + braunL k := by
  have hdec (j : Fin 4) :
      scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) j =
        scheduleLoads (m := 4) (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k))
          (appendAssign (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
            (fun _ => 3) (diagAssignReplicate (m := 4) (braunL k))) j +
        scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => ⟨i.1, by omega⟩) j := by
    dsimp only [braunSkTrapWitness, braunSkTrapAssign]
    rw [scheduleLoads_append (m := 4) (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k))
      (List.replicate 3 (braunS k))
      (appendAssign (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
        (fun _ => 3) (diagAssignReplicate (m := 4) (braunL k)))
      (fun i : Fin 3 => ⟨i.1, by omega⟩) j]
  have hdec2 (j : Fin 4) :
      scheduleLoads (m := 4) (braunPrefixSp (k - 1) ++ List.replicate 4 (braunL k))
        (appendAssign (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
          (fun _ => 3) (diagAssignReplicate (m := 4) (braunL k))) j =
        scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3) j +
        scheduleLoads (m := 4) (List.replicate 4 (braunL k)) (diagAssignReplicate (m := 4) (braunL k)) j := by
    rw [scheduleLoads_append (m := 4) (braunPrefixSp (k - 1)) (List.replicate 4 (braunL k))
      (fun _ => 3) (diagAssignReplicate (m := 4) (braunL k)) j]
  have hprefix (j : Fin 4) :
      scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ : Fin (braunPrefixSp (k - 1)).length => (3 : Fin 4)) j =
        (if j = 3 then totalLoad (braunPrefixSp (k - 1)) else 0) := by
    by_cases hj : j = 3
    · subst hj
      have hsum := sum_scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3)
      have h3 := fin4_sum_extract3 (fun j' => scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3) j')
      rw [h3, hsum]
      have hz0 : scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3) 0 = 0 := by
        apply scheduleLoads_zero_of_forall_ne
        intro i
        decide
      have hz1 : scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3) 1 = 0 := by
        apply scheduleLoads_zero_of_forall_ne
        intro i
        decide
      have hz2 : scheduleLoads (m := 4) (braunPrefixSp (k - 1)) (fun _ => 3) 2 = 0 := by
        apply scheduleLoads_zero_of_forall_ne
        intro i
        decide
      rw [hz0, hz1, hz2]
      simp
    · have hne : ∀ i : Fin (braunPrefixSp (k - 1)).length, (3 : Fin 4) ≠ j := by
        intro i
        intro h
        exact hj h.symm
      have hz := scheduleLoads_zero_of_forall_ne (braunPrefixSp (k - 1)) (fun _ => 3) j hne
      rw [hz]
      simp [hj]
  have hLpart (j : Fin 4) :
      scheduleLoads (m := 4) (List.replicate 4 (braunL k)) (diagAssignReplicate (m := 4) (braunL k)) j = braunL k := by
    rw [scheduleLoads_replicate_diag (m := 4) (braunL k)]
  have hS0 : scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => ⟨i.1, by omega⟩) 0 = braunS k := by
    dsimp only [scheduleLoads]
    change (∑ i : Fin 3, if (⟨i.1, by omega⟩ : Fin 4) = 0 then (List.replicate 3 (braunS k))[i] else 0) = braunS k
    rw [Fin.sum_univ_three]
    simp
  have hS1 : scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => ⟨i.1, by omega⟩) 1 = braunS k := by
    dsimp only [scheduleLoads]
    change (∑ i : Fin 3, if (⟨i.1, by omega⟩ : Fin 4) = 1 then (List.replicate 3 (braunS k))[i] else 0) = braunS k
    rw [Fin.sum_univ_three]
    simp
  have hS2 : scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => ⟨i.1, by omega⟩) 2 = braunS k := by
    dsimp only [scheduleLoads]
    change (∑ i : Fin 3, if (⟨i.1, by omega⟩ : Fin 4) = 2 then (List.replicate 3 (braunS k))[i] else 0) = braunS k
    rw [Fin.sum_univ_three]
    simp
  have hS3 : scheduleLoads (m := 4) (List.replicate 3 (braunS k)) (fun i : Fin 3 => ⟨i.1, by omega⟩) 3 = 0 := by
    dsimp only [scheduleLoads]
    change (∑ i : Fin 3, if (⟨i.1, by omega⟩ : Fin 4) = 3 then (List.replicate 3 (braunS k))[i] else 0) = 0
    rw [Fin.sum_univ_three]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdec 0, hdec2 0, hLpart 0, hS0, hprefix 0]
    simp
  · rw [hdec 1, hdec2 1, hLpart 1, hS1, hprefix 1]
    simp
  · rw [hdec 2, hdec2 2, hLpart 2, hS2, hprefix 2]
    simp
  · rw [hdec 3, hdec2 3, hLpart 3, hS3, hprefix 3]
    simp

/-- OPT of the S_k-trap witness is at most S_k + L_k (k ≥ 1). -/
lemma braun_opt_Sk_trap_le (k : ℕ) (hk : 1 ≤ k) :
    optMakespan (m := 4) (braunSkTrapWitness k) ≤ braunS k + braunL k := by
  have hle := optMakespan_le_of_schedule (m := 4) (braunSkTrapWitness k)
    (scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k)) (braunSkTrapAssign k) rfl
  refine le_trans hle ?_
  dsimp only [makespan]
  refine Finset.sup'_le _ _ (fun j hj => ?_)
  rcases braunSkTrapAssign_loads k with ⟨h0, h1, h2, h3⟩
  fin_cases j
  · change scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 0 ≤ braunS k + braunL k
    nlinarith [h0]
  · change scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 1 ≤ braunS k + braunL k
    nlinarith [h1]
  · change scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 2 ≤ braunS k + braunL k
    nlinarith [h2]
  · change scheduleLoads (m := 4) (braunSkTrapWitness k) (braunSkTrapAssign k) 3 ≤ braunS k + braunL k
    nlinarith [h3, braun_prefix_total_le_S k hk]

/-! ### Layer-k forcing step (k ≥ 2) -/

/-- Layer-k forcing (k ≥ 2): from loads ≥ Φ_{k−1} after `braunPrefixSp (k−1)`,
    the block {L_k×4, S_k×3, S⁺_k} either yields a witness achieving the additive
    bound (a prefix of `braunPrefixSp k`), or leaves every machine at load ≥ Φ_k. -/
lemma braun_layerk_forcing_pref (k : ℕ) (hk : 2 ≤ k) (alg : OnlineAlgorithm 4)
    (hinv : ∀ i : Fin 4, braunSumLS (k - 1) ≤ runAlgorithm 4 alg (braunPrefixSp (k - 1)) i) :
    (∃ σ : JobSequence, List.IsPrefix σ (braunPrefixSp k) ∧
        Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, braunSumLS k ≤ runAlgorithm 4 alg (braunPrefixSp k) i) := by
  have hkpos : 1 ≤ k := by omega
  rcases braun_layer_separation_lb alg (braunSumLS (k - 1)) (braunL k) (braunL_pos k)
      (runAlgorithm 4 alg (braunPrefixSp (k - 1))) hinv with hLbad | hLgood
  · left
    refine ⟨braunLkTrapWitness k, braun_L_witness_prefix k hkpos, ?_⟩
    have hmk : braunSumLS (k - 1) + 2 * braunL k ≤ algorithmMakespan 4 alg (braunLkTrapWitness k) := by
      dsimp only [algorithmMakespan, runAlgorithm, braunLkTrapWitness]
      rw [List.foldl_append]
      exact hLbad
    have hopt := braun_opt_Lk_trap_le k hk
    have hsq : Real.sqrt 3 * optMakespan (m := 4) (braunLkTrapWitness k) ≤
        Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) :=
      mul_le_mul_of_nonneg_left hopt (le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))
    calc
      Real.sqrt 3 * optMakespan (m := 4) (braunLkTrapWitness k) - (2 - Real.sqrt 3)
          ≤ Real.sqrt 3 * (braunSp (k - 1) + braunL (k - 1) + braunL k) - (2 - Real.sqrt 3) := by linarith
      _ ≤ braunSumLS (k - 1) + 2 * braunL k := braun_trap_Lk k hk
      _ ≤ algorithmMakespan 4 alg (braunLkTrapWitness k) := hmk
  · have hLgood' : ∀ i : Fin 4, braunSumLS (k - 1) + braunL k ≤
        ((List.replicate 4 (braunL k)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (braunPrefixSp (k - 1)))) i := by
      intro i
      rw [hLgood i]
      nlinarith [hinv i]
    rcases braun_three_from_lb alg (braunSumLS (k - 1) + braunL k) (braunS k) (braunS_pos k)
        ((List.replicate 4 (braunL k)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (braunPrefixSp (k - 1)))) hLgood'
        with hSbad | hSgood
    · left
      refine ⟨braunSkTrapWitness k, braun_S_witness_prefix k hkpos, ?_⟩
      have hmk : braunSumLS (k - 1) + braunL k + 2 * braunS k ≤
          algorithmMakespan 4 alg (braunSkTrapWitness k) := by
        dsimp only [algorithmMakespan, runAlgorithm, braunSkTrapWitness]
        rw [List.foldl_append, List.foldl_append]
        exact hSbad
      have hopt := braun_opt_Sk_trap_le k hkpos
      have hsq : Real.sqrt 3 * optMakespan (m := 4) (braunSkTrapWitness k) ≤
          Real.sqrt 3 * (braunS k + braunL k) :=
        mul_le_mul_of_nonneg_left hopt (le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))
      calc
        Real.sqrt 3 * optMakespan (m := 4) (braunSkTrapWitness k) - (2 - Real.sqrt 3)
            ≤ Real.sqrt 3 * (braunS k + braunL k) - (2 - Real.sqrt 3) := by linarith
        _ ≤ braunSumLS (k - 1) + braunL k + 2 * braunS k := braun_trap_Sk k hkpos
        _ ≤ algorithmMakespan 4 alg (braunSkTrapWitness k) := hmk
    · rcases hSgood with ⟨j0, hj0base, hj0rest⟩
      let l2 : Loads 4 := (List.replicate 3 (braunS k)).foldl (step (m := 4) alg)
        ((List.replicate 4 (braunL k)).foldl (step (m := 4) alg) (runAlgorithm 4 alg (braunPrefixSp (k - 1))))
      have hj0base' : braunSumLS (k - 1) + braunL k ≤ l2 j0 := by
        dsimp only [l2]
        rw [hj0base]
        rw [hLgood j0]
        nlinarith [hinv j0]
      have hj0rest' : ∀ i : Fin 4, i ≠ j0 → braunSumLS (k - 1) + braunL k + braunS k ≤ l2 i := by
        intro i hi
        dsimp only [l2]
        rw [hj0rest i hi]
        rw [hLgood i]
        nlinarith [hinv i]
      have hsumk : braunSumLS k = braunSumLS (k - 1) + (braunL k + braunS k) := by
        rw [show braunSumLS k = (∑ x ∈ Finset.range k, (braunL x + braunS x)) + (braunL k + braunS k) by
          dsimp [braunSumLS]
          rw [Finset.sum_range_succ]]
        rw [show (∑ x ∈ Finset.range k, (braunL x + braunS x)) = braunSumLS (k - 1) by
          dsimp [braunSumLS]
          rw [show (k - 1) + 1 = k by omega]]
      by_cases hjj0 : alg l2 (braunSp k) = j0
      · right
        intro i
        have hrun : runAlgorithm 4 alg (braunPrefixSp k) i = step (m := 4) alg l2 (braunSp k) i := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          dsimp only [braunPrefixSp, braunLayerBlock, runAlgorithm, l2]
          rw [show (k - 1) + 1 = k by omega]
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hrun]
        by_cases hij0 : i = j0
        · dsimp only [step]
          rw [if_pos (by rw [hij0]; exact hjj0.symm)]
          rw [hij0]
          have hle : braunSumLS k ≤ braunSumLS (k - 1) + braunL k + braunSp k := by
            rw [hsumk]
            nlinarith [braunS_le_braunSp k]
          exact le_trans hle (by nlinarith [hj0base'])
        · dsimp only [step]
          rw [if_neg (by
            intro h
            have : i = j0 := by rw [h, hjj0]
            exact hij0 this)]
          rw [hsumk]
          nlinarith [hj0rest' i hij0]
      · left
        refine ⟨braunPrefixSp k, braun_isPrefix_refl (braunPrefixSp k), ?_⟩
        have hjj0' : alg l2 (braunSp k) ≠ j0 := hjj0
        have hrunj : runAlgorithm 4 alg (braunPrefixSp k) (alg l2 (braunSp k)) = step (m := 4) alg l2 (braunSp k) (alg l2 (braunSp k)) := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          dsimp only [braunPrefixSp, braunLayerBlock, runAlgorithm, l2]
          rw [show (k - 1) + 1 = k by omega]
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hloadj : braunSumLS k + braunSp k ≤ runAlgorithm 4 alg (braunPrefixSp k) (alg l2 (braunSp k)) := by
          rw [hrunj]
          dsimp only [step]
          rw [if_pos rfl]
          rw [hsumk]
          nlinarith [hj0rest' (alg l2 (braunSp k)) hjj0']
        have hmk : braunSumLS k + braunSp k ≤ algorithmMakespan 4 alg (braunPrefixSp k) := by
          dsimp only [algorithmMakespan]
          exact le_trans hloadj (makespan_ge_each (m := 4) (runAlgorithm 4 alg (braunPrefixSp k)) (alg l2 (braunSp k)))
        have hid := braun_prefix_additive_identity k hkpos
        have hoptS := braun_opt_prefix_Sp k hkpos
        calc
          Real.sqrt 3 * optMakespan (m := 4) (braunPrefixSp k) - (2 - Real.sqrt 3)
              = Real.sqrt 3 * (braunSp k + braunL k) - (2 - Real.sqrt 3) := by rw [hoptS]
          _ = braunSumLS k + braunSp k := by rw [hid]
          _ ≤ algorithmMakespan 4 alg (braunPrefixSp k) := hmk

/-! ### The full induction over layers 0..r -/

/-- The general-r forced induction: either some layer deviates and yields a
    witness prefix of `braunPrefixSp r` achieving the additive bound, or the
    algorithm follows the Table 3 schedule and every machine ends at ≥ Φ_r. -/
lemma braun_force_general_pref (r : ℕ) (alg : OnlineAlgorithm 4) :
    (∃ σ : JobSequence, List.IsPrefix σ (braunPrefixSp r) ∧
        Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ) ∨
    (∀ i : Fin 4, braunSumLS r ≤ runAlgorithm 4 alg (braunPrefixSp r) i) := by
  rcases braun_base_forcing_pref alg with hb | hb0
  · rcases hb with ⟨σ, hpref, hbound⟩
    exact Or.inl ⟨σ, braun_isPrefix_trans hpref (braun_prefix_mono (Nat.zero_le r)), hbound⟩
  · revert hb0
    induction r with
    | zero =>
        intro hb0
        right
        intro i
        exact le_of_eq (hb0 i).symm
    | succ r ih =>
        intro hb0
        rcases ih hb0 with hwit | hinv
        · rcases hwit with ⟨σ, hpref, hb⟩
          exact Or.inl ⟨σ, braun_isPrefix_trans hpref (braun_prefix_step r), hb⟩
        · by_cases hr : r = 0
          · subst hr
            rcases braun_layer1_forcing_pref alg hb0 with hw | hc
            · exact Or.inl hw
            · right
              intro i
              exact hc i
          · have hge : 2 ≤ r + 1 := by omega
            rcases braun_layerk_forcing_pref (r + 1) hge alg hinv with hw | hc
            · exact Or.inl hw
            · right
              intro i
              exact hc i

/-- Theorem 1 for the full parameter family (adaptive adversary): for every r
    and every deterministic online algorithm on 4 machines there is a prefix of
    σ_r (n = 8r+9 jobs) whose makespan reaches √3·OPT − (2−√3). The adversary
    runs the paper's Table 3 forced-schedule induction: a deviation at any L_k
    or S_k layer stops with the corresponding trap, a deviation at S⁺_k stops
    with the exact additive trap, and a clean schedule is finished off by F. -/
theorem braun_asymptotic_lower_bound_general (r : ℕ) (alg : OnlineAlgorithm 4) :
    ∃ σ : JobSequence, List.IsPrefix σ (braunSeq r) ∧
      Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ := by
  rcases braun_force_general_pref r alg with hwit | hclean
  · rcases hwit with ⟨σ, hpref, hb⟩
    exact ⟨σ, braun_isPrefix_trans hpref (braun_prefix_seq r), hb⟩
  · refine ⟨braunSeq r, braun_isPrefix_refl (braunSeq r), ?_⟩
    have hload : braunSumLS r + braunF r ≤ algorithmMakespan 4 alg (braunSeq r) := by
      have hseq : braunSeq r = braunPrefixSp r ++ [braunF r] := by
        dsimp only [braunSeq]
        rw [← braunPrefixSp_eq_flat r]
      dsimp only [algorithmMakespan]
      rw [hseq, runAlgorithm, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      let j : Fin 4 := alg (runAlgorithm 4 alg (braunPrefixSp r)) (braunF r)
      have hstepj : braunSumLS r + braunF r ≤
          step (m := 4) alg (runAlgorithm 4 alg (braunPrefixSp r)) (braunF r) j := by
        dsimp only [step]
        rw [if_pos rfl]
        nlinarith [hclean j]
      exact le_trans hstepj (makespan_ge_each (m := 4) (step (m := 4) alg (runAlgorithm 4 alg (braunPrefixSp r)) (braunF r)) j)
    have hid := braun_additive_identity r
    have hoptF := braun_opt_eq_F r
    calc
      Real.sqrt 3 * optMakespan (m := 4) (braunSeq r) - (2 - Real.sqrt 3)
          = Real.sqrt 3 * braunF r - (2 - Real.sqrt 3) := by rw [hoptF]
      _ = braunForcedMakespan r := by rw [hid]
      _ = braunSumLS r + braunF r := by rfl
      _ ≤ algorithmMakespan 4 alg (braunSeq r) := hload

/-- Theorem 1 (Braun–Chung–Graham 2025): for every deterministic online algorithm
    on 4 machines there is a task sequence with makespan ≥ √3·OPT − (2−√3)
    (the r = 1 instance of the general adaptive adversary). -/
theorem braun_asymptotic_lower_bound (alg : OnlineAlgorithm 4) :
    ∃ σ : JobSequence,
      Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ := by
  rcases braun_asymptotic_lower_bound_general 1 alg with ⟨σ, hpref, hb⟩
  exact ⟨σ, hb⟩

end
