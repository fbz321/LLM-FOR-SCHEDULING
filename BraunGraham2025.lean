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

/-- OPT of σ_r is at most F (Table-7 packing upper bound). -/
theorem braun_opt_le_F (r : ℕ) :
    optMakespan (m := 4) (braunSeq r) ≤ braunF r := by
  -- 用 braunAssign 作为 witness
  have hle := optMakespan_le_of_schedule (m := 4) (braunSeq r)
    (scheduleLoads (m := 4) (braunSeq r) (braunAssign r)) (braunAssign r) rfl
  -- makespan (scheduleLoads σ braunAssign) ≤ F：每台负载 ≤ F
  have hm : makespan 4 (scheduleLoads (m := 4) (braunSeq r) (braunAssign r)) ≤ braunF r := by
    dsimp [makespan]
    refine Finset.sup'_le _ _ (fun j hj => ?_)
    -- 每台负载 ≤ F：四机分情况（见 braunBlockAssign_loads / M1 / M2 / M3 恒等式）
    have hdec := braunAssign_loads_decomp r j
    fin_cases j
    · -- 机器 0：只有 F，负载 = F ≤ F（组装：scheduleLoads 展开后其余段贡献 0）
      sorry
    · -- 机器 1：2S₀ + Σ(2L_k + S⁺_k) = F（braun_M1_eq_F）
      sorry
    · -- 机器 2：2S_r = F（blocks 顶层给 M2 两个 S_r；需对 t∈range r 求和，
      --   只有 t+1=r 时 braunBlockAssign 给 M2 非零。纯机械，留待下一步）
      sorry
    · -- 机器 3：4L₀ + 2S₀ + 其余 < F（braun_M3_lt_F）
      sorry
  exact le_trans hle hm

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

end
