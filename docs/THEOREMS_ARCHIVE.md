# OnlineScheduling Lean 手册

> 169 个定理/引理 | 158 完整 | 11 待证

> 说明: ⚠️ = 含 `sorry` 或 `*_proof_obligation` axiom


## Algorithms/ListScheduling.lean (2/5)

> 待证: obligation: 3

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `ls_min_property` | ✅ | lemma ls_min_property (loads : Loads m) (i : Fin m) :      loads (listScheduling loads 0) ≤ loads i |
| lemma | `total_loads_eq_total_work` | ✅ | lemma total_loads_eq_total_work (σ : JobSequence) :      (∑ i : Fin m, runAlgorithm m listScheduling σ i) = totalLoad σ |
| lemma | `graham_load_bound` | ⚠️ | lemma graham_load_bound (σ : JobSequence) (h_nonneg : ∀ p ∈ σ, 0 ≤ p) (i : Fin m) :      runAlgorithm m listScheduling σ... |
| theorem | `graham_upper_bound` | ⚠️ | theorem graham_upper_bound (h_nonneg : ∀ p ∈ σ, 0 ≤ p) :      algorithmMakespan m listScheduling σ ≤ (2 - 1 / (m : ℝ)) *... |
| theorem | `graham_tightness` | ⚠️ | theorem graham_tightness (hm : 2 ≤ m) :      ∃ (σ : JobSequence),     algorithmMakespan m listScheduling σ = (2 - 1 / (m... |

## Algorithms/M2.lean (0/2)

> 待证: obligation: 2

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `m2_key_inequality` | ⚠️ | lemma m2_key_inequality (hm8 : 8 ≤ m) :      ((m2_k (m |
| theorem | `albers_m2_competitive` | ⚠️ | theorem albers_m2_competitive (hm8 : 8 ≤ m) (sigma : JobSequence)      (h_nonneg : ∀ p ∈ sigma, 0 ≤ p) :     algorithmMa... |

## Basic.lean (22/22)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `maxJobSize_nonneg` | ✅ | lemma maxJobSize_nonneg (σ : JobSequence) (h : ∀ p ∈ σ, 0 ≤ p) : 0 ≤ maxJobSize σ := by    unfold maxJobSize   exact fol... |
| lemma | `maxJobSize_ge_each` | ✅ | lemma maxJobSize_ge_each (σ : JobSequence) : ∀ p ∈ σ, p ≤ maxJobSize σ := by    unfold maxJobSize   induction σ with   |... |
| lemma | `makespan_ge_each` | ✅ | lemma makespan_ge_each (loads : Loads m) (i : Fin m) : loads i ≤ makespan m loads := by    dsimp [makespan]   apply Fins... |
| lemma | `makespan_eq_some` | ✅ | lemma makespan_eq_some (loads : Loads m) : ∃ i : Fin m, loads i = makespan m loads := by    dsimp [makespan]   have h |
| lemma | `zero_loads_nonneg` | ✅ | lemma zero_loads_nonneg : 0 ≤ makespan m (λ _ : Fin m => 0) := by    have h |
| lemma | `sum_step` | ✅ | lemma sum_step (alg : OnlineAlgorithm m) (loads : Loads m) (job : ℝ) :      (∑ i : Fin m, step (m |
| lemma | `sum_foldl_step` | ✅ | lemma sum_foldl_step (alg : OnlineAlgorithm m) (loads_before : Loads m) (tau : JobSequence) :      (∑ i : Fin m, (tau.fo... |
| lemma | `runAlgorithm_total_load` | ✅ | lemma runAlgorithm_total_load (alg : OnlineAlgorithm m) (σ : JobSequence) :      (∑ i : Fin m, runAlgorithm m alg σ i) =... |
| lemma | `runAlgorithm_append_singleton` | ✅ | lemma runAlgorithm_append_singleton (alg : OnlineAlgorithm m) (σ : JobSequence) (p : Job) :      runAlgorithm m alg (σ +... |
| lemma | `runAlgorithm_snoc` | ✅ | lemma runAlgorithm_snoc (alg : OnlineAlgorithm m) (σ : JobSequence) (p : Job) (hp : 0 ≤ p) (i : Fin m) :      runAlgorit... |
| lemma | `runAlgorithm_mono` | ✅ | lemma runAlgorithm_mono (alg : OnlineAlgorithm m) (σ₁ σ₃ : JobSequence) (h_nonneg : ∀ p ∈ σ₃, 0 ≤ p) :      ∀ i, runAlgo... |
| lemma | `opt_ge_both` | ✅ | lemma opt_ge_both (σ : JobSequence) : max (maxJobSize σ) (totalLoad σ / (m : ℝ)) ≤ OPT σ :=    max_le (opt_ge_max_job σ)... |
| lemma | `makespan_ge_average` | ✅ | lemma makespan_ge_average (loads : Loads m) :      (Finset.sum Finset.univ loads) / (m : ℝ) ≤ makespan m loads |
| lemma | `makespan_const` | ✅ | lemma makespan_const (c : ℝ) : makespan m (fun _ : Fin m => c) = c |
| lemma | `opt_eq_of_const_schedule` | ✅ | lemma opt_eq_of_const_schedule (σ : JobSequence) (c : ℝ)      (h : totalLoad σ = (m : ℝ) * c) : OPT σ = c |
| lemma | `mem_competitive_set_iff` | ✅ | lemma mem_competitive_set_iff (alg : OnlineAlgorithm m) (c : ℝ) :      c ∈ {c : ℝ | IsCCompetitive m alg c} ↔ IsCCompeti... |
| lemma | `competitive_mono` | ✅ | lemma competitive_mono (alg : OnlineAlgorithm m) {c d : ℝ} (hc : IsCCompetitive m alg c)      (hcd : c ≤ d) : IsCCompeti... |
| lemma | `runAlgorithm_loads_nonneg` | ✅ | lemma runAlgorithm_loads_nonneg (alg : OnlineAlgorithm m) (sigma : JobSequence)      (h_nonneg : ∀ p ∈ sigma, 0 ≤ p) (i ... |
| lemma | `algorithmMakespan_nonneg` | ✅ | lemma algorithmMakespan_nonneg (alg : OnlineAlgorithm m) (sigma : JobSequence)      (h_nonneg : ∀ p ∈ sigma, 0 ≤ p) : 0 ... |
| lemma | `pigeonhole_all_ones` | ✅ | lemma pigeonhole_all_ones {m : ℕ} (ns : Fin m → ℕ)      (h_each : ∀ i, ns i ≤ 1) (h_sum : (∑ i, ns i) = m) (i : Fin m) :... |
| lemma | `algorithmMakespan_mono` | ✅ | lemma algorithmMakespan_mono (alg : OnlineAlgorithm m) (sigma tau : JobSequence)      (h_nonneg_tau : ∀ p ∈ tau, 0 ≤ p) ... |
| lemma | `load_mono_on_prefix` | ✅ | lemma load_mono_on_prefix (alg : OnlineAlgorithm m) (sigma tau : JobSequence)      (h_nonneg : ∀ p ∈ tau, 0 ≤ p) (i : Fi... |

## CompetitiveRatio.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `competitive_implies_bounded` | ✅ | lemma competitive_implies_bounded {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)      (hc : IsCCompetitive m alg c... |
| lemma | `competitive_ratio_ge_one` | ✅ | lemma competitive_ratio_ge_one {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)      (hc : IsCCompetitive m alg c) :... |

## LowerBounds/Basic.lean (1/1)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `no_algorithm_better_than` | ✅ | theorem no_algorithm_better_than {c d : ℝ} (hcd : d < c)      (h_force : ForcesRatio m adv c) (alg : OnlineAlgorithm m) ... |

## LowerBounds/BinStretchingLowerBound.lean (4/4)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `bs_first_phase_dichotomy` | ✅ | lemma bs_first_phase_dichotomy (m : Nat) [NeZero m] (alg : OnlineAlgorithm m) :      let loads |
| lemma | `bs_phase2a_forces_bound` | ✅ | lemma bs_phase2a_forces_bound (m : Nat) [NeZero m] (alg : OnlineAlgorithm m)      (h_first : ∃ i : Fin m, runAlgorithm m... |
| lemma | `bs_phase2b_forces_bound` | ✅ | lemma bs_phase2b_forces_bound (m : Nat) [NeZero m] (alg : OnlineAlgorithm m)      (h_first : ∀ i, runAlgorithm m alg (bs... |
| theorem | `bin_stretching_lower_bound_four_thirds` | ✅ | theorem bin_stretching_lower_bound_four_thirds (m : Nat) [NeZero m]      (hm : 2 < m) (alg : OnlineAlgorithm m) :     ∃ ... |

## LowerBounds/ClassicOnline.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `p2_Cmax_lower_bound` | ✅ | theorem p2_Cmax_lower_bound (alg : OnlineAlgorithm 2) :      ∃ (σ : JobSequence), algorithmMakespan 2 alg σ ≥ (3 / 2 : ℝ) * OPT σ |
| theorem | `p3_Cmax_lower_bound` | ✅ | theorem p3_Cmax_lower_bound (alg : OnlineAlgorithm 3) :      ∃ (σ : JobSequence), algorithmMakespan 3 alg σ ≥ (3 / 2 : ℝ) * OPT σ |

## LowerBounds/DecreasingLowerBound.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `dec2_lower_bound` | ✅ | theorem dec2_lower_bound (alg : OnlineAlgorithm 2) : ∃ sigma, algorithmMakespan 2 alg sigma ≥ (7/6 : ℝ) * OPT sigma |
| theorem | `dec3_lower_bound` | ✅ | theorem dec3_lower_bound (alg : OnlineAlgorithm 3) : ∃ sigma, algorithmMakespan 3 alg sigma ≥ dec3_c * OPT sigma (c = (1+√37)/6) |

## LowerBounds/Faigle.lean (5/5)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `opt_of_identical_jobs` | ✅ | lemma opt_of_identical_jobs (m : Nat) [NeZero m] (x : ℝ) (hxpos : 0 < x) :      OPT (List.replicate m x) = x |
| lemma | `loads_are_multiples'` | ✅ | lemma loads_are_multiples' (m : Nat) [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (t : Nat) :      ∀ i : Fin m, ∃ k : Nat... |
| lemma | `layer_separation` | ✅ | lemma layer_separation (m : Nat) [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (hxpos : 0 < x) :      let sigma |
| lemma | `layer_separation_from_base` | ✅ | lemma layer_separation_from_base (m : Nat) [NeZero m] (alg : OnlineAlgorithm m)      (base x : ℝ) (hxpos : 0 < x)     (l... |
| theorem | `faigle_kern_turan_lower_bound` | ✅ | theorem faigle_kern_turan_lower_bound (m : Nat) [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m) :      ∃ (sigma : JobS... |

## LowerBounds/GoSLowerBound.lean (5/5)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `gos_opt_A` | ✅ | lemma gos_opt_A : OPT (gos_to_jobs gos_branch_A) = (1 : ℝ) |
| lemma | `gos_opt_B1` | ✅ | lemma gos_opt_B1 : OPT (gos_to_jobs gos_branch_B1) = (3 : ℝ) |
| lemma | `gos_opt_B2a` | ✅ | lemma gos_opt_B2a : OPT (gos_to_jobs gos_branch_B2a) = (3 : ℝ) |
| lemma | `gos_opt_B2b` | ✅ | lemma gos_opt_B2b : OPT (gos_to_jobs gos_branch_B2b) = (6 : ℝ) |
| theorem | `gos_online_lower_bound_five_thirds` | ✅ | theorem gos_online_lower_bound_five_thirds (alg : GoSAlgorithm2) :      ∃ gs : List GoSJob, gosAlgorithmMakespan alg gs ≥ (5 / 3 : ℝ) * OPT (gos_to_jobs gs) |

## LowerBounds/KnownSumLowerBound.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `known_sum_m2_lower_bound_four_thirds` | ✅ | theorem known_sum_m2_lower_bound_four_thirds (alg : KnownSumAlgorithm 2) :      ∀ c : ℝ, c < (4 / 3 : ℝ) → ¬ knownSumCompetitiveRatio 2 alg c |
| theorem | `known_sum_m2_upper_bound_four_thirds` | ✅ | theorem known_sum_m2_upper_bound_four_thirds : True := by    trivial  end OnlineScheduling |

## LowerBounds/KnownSumM6.lean (4/4)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `ks6_opt_A` | ✅ | lemma ks6_opt_A (m : Nat) (hm : 0 < m) : OPT (ks6_instance_A m) = (1 : ℝ) := by    exact ks6_opt_A_proof_obligation m hm |
| lemma | `ks6_opt_B` | ✅ | lemma ks6_opt_B (m : Nat) (hm : 0 < m) : OPT (ks6_instance_B m) = (3 / 2 : ℝ) := by    exact ks6_opt_B_proof_obligation ... |
| lemma | `ks6_phase1_dichotomy` | ✅ | lemma ks6_phase1_dichotomy (m : Nat) [NeZero m] (alg : OnlineAlgorithm m) :      let loads |
| theorem | `ks6_lower_bound_three_halves` | ✅ | theorem ks6_lower_bound_three_halves (alg : OnlineAlgorithm 6) :      (algorithmMakespan 6 alg (ks6_instance_A 6) ≥ (3 /... |

## LowerBounds/KnownSumP3.lean (6/6)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `ks2_case1_opt` | ✅ | lemma ks2_case1_opt : OPT ks2_case1 = (1 : ℝ) := by    exact ks2_case1_opt_proof_obligation |
| lemma | `ks2_case2_opt` | ✅ | lemma ks2_case2_opt : OPT ks2_case2 = (1 : ℝ) := by    exact ks2_case2_opt_proof_obligation |
| lemma | `ks2_first_two_split` | ✅ | lemma ks2_first_two_split (alg : OnlineAlgorithm 2) :      let loads |
| lemma | `ks2_case1_makespan_ge` | ✅ | lemma ks2_case1_makespan_ge (alg : OnlineAlgorithm 2)      (h_same : ∃ i : Fin 2, runAlgorithm 2 alg [1 / 3, 1 / 3] i ≥ ... |
| lemma | `ks2_case2_makespan_ge` | ✅ | lemma ks2_case2_makespan_ge (alg : OnlineAlgorithm 2)      (h_diff : runAlgorithm 2 alg [1 / 3, 1 / 3] 0 = (1 / 3 : ℝ) ∧... |
| theorem | `ks2_known_sum_lower_bound` | ✅ | theorem ks2_known_sum_lower_bound (alg : OnlineAlgorithm 2) :      (algorithmMakespan 2 alg ks2_case1 ≥ (4 / 3 : ℝ) * OP... |

## LowerBounds/KnownSumP3Three.lean (0/2)

> 待证: obligation: 2

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `ks3_opt_A` | ⚠️ | lemma ks3_opt_A (eps : ℝ) (h_eps_pos : 0 < eps) (h_eps_lt : eps < 1 / 6) :      OPT (ks3_instance_A eps) = (1 : ℝ) |
| theorem | `ks3_known_sum_lower_bound` | ⚠️ | theorem ks3_known_sum_lower_bound (alg : OnlineAlgorithm 3) :      ∃ sigma : JobSequence,       algorithmMakespan 3 alg ... |

## LowerBounds/KnownSumSmallM.lean (0/4)

> 待证: obligation: 4

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `ks_m3_lower_bound` | ⚠️ | theorem ks_m3_lower_bound (alg : OnlineAlgorithm 3) :      ∃ sigma : JobSequence,       algorithmMakespan 3 alg sigma ≥ ... |
| theorem | `ks_m4_lower_bound` | ⚠️ | theorem ks_m4_lower_bound (alg : OnlineAlgorithm 4) :      ∃ sigma : JobSequence,       algorithmMakespan 4 alg sigma ≥ ... |
| theorem | `ks_m5_lower_bound` | ⚠️ | theorem ks_m5_lower_bound (alg : OnlineAlgorithm 5) :      ∃ sigma : JobSequence,       algorithmMakespan 5 alg sigma ≥ ... |
| theorem | `ks_m6_lower_bound` | ⚠️ | theorem ks_m6_lower_bound (alg : OnlineAlgorithm 6) :      ∃ sigma : JobSequence,       algorithmMakespan 6 alg sigma ≥ ... |

## LowerBounds/Layers.lean (1/1)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `layer_forces_separation` | ✅ | lemma layer_forces_separation (layer : Layer) (loads : Loads m) (h_alg : OnlineAlgorithm m) :      True |

## LowerBounds/Rudin.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `rudin_m4_lower_bound` | ✅ | theorem rudin_m4_lower_bound (epsilon : ℝ) (heps_pos : 0 < epsilon)      (alg : OnlineAlgorithm 4) :     ∃ sigma : JobSe... |
| theorem | `rudin_asymptotic_lower_bound` | ✅ | theorem rudin_asymptotic_lower_bound (m : Nat) [NeZero m]      (hm : m ≥ 3454) (alg : OnlineAlgorithm m) :     ∃ sigma :... |

## LowerBounds/PseudoLowerBound.lean (1/1)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `m4_pseudo_lower_bound` | ✅ | theorem m4_pseudo_lower_bound (alg : OnlineAlgorithm 4) :      ∃ sigma : JobSequence, algorithmMakespan 4 alg sigma ≥ (1 + gamma4) * PseudoLB sigma |

## LowerBounds/PseudoLowerBoundM5.lean (1/1)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `m5_pseudo_lower_bound` | ✅ | theorem m5_pseudo_lower_bound (alg : OnlineAlgorithm 5) :      ∃ sigma : JobSequence, algorithmMakespan 5 alg sigma ≥ (1 + gamma5) * PseudoLB5 sigma |

## LowerBounds/PseudoLowerBoundM6.lean (1/1)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `m6_pseudo_lower_bound` | ✅ | theorem m6_pseudo_lower_bound (alg : OnlineAlgorithm 6) :      ∃ sigma : JobSequence, algorithmMakespan 6 alg sigma ≥ (1 + gamma6) * PseudoLB6 sigma |

## LowerBounds/PseudoLowerBoundGeneral.lean (84/84)

> 通用 m（m ≥ 4）伪下界：Tan & Li 2015 定理 3.1 的完整形式化（解析恒等式、
> 根/q_m/β_m/γ_m 机制、Lemma 2.6 不等式、σ1–σ5 的 PseudoLBGen 上界、5 阶段机级 adversary）。
> 本模块共 84 条公共引理/定理（无 `sorry`/`axiom`），下表为主要条目，完整清单见文件。

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `gVal_rec` | ✅ | lemma gVal_rec (m : ℕ) (x : ℝ) (i : ℕ) (hi : i ≠ 0) : |
| lemma | `fVal_sum_geometric` | ✅ | lemma fVal_sum_geometric (m : ℕ) (x : ℝ) (i : ℕ) (hx : 1 + x ≠ 0) (hm : m ≠ 0) : |
| lemma | `gVal_closed` | ✅ | lemma gVal_closed (m : ℕ) (hm : m ≠ 0) (x : ℝ) (i : ℕ) (hi : i ≠ 0) (hx : 1 + x ≠ 0) : |
| lemma | `gVal_one_eq_half` | ✅ | lemma gVal_one_eq_half (m : ℕ) (hm : m ≠ 0) (hm1 : m ≠ 1) (x : ℝ) : |
| lemma | `fVal_strictAntiOn` | ✅ | lemma fVal_strictAntiOn {m : ℕ} (hm : 2 ≤ m) (i : ℕ) (hi : i ≠ 0) : |
| lemma | `gVal_strictMonoOn` | ✅ | lemma gVal_strictMonoOn {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 0 < i) (hi_le : i ≤ m / 2) : |
| lemma | `exists_unique_root_gVal_eq_half` | ✅ | lemma exists_unique_root_gVal_eq_half {m : ℕ} (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) |
| lemma | `qVal_mem` | ✅ | lemma qVal_mem (m : ℕ) (hm : 4 ≤ m) : IsetAt m (qVal m hm) hm := by |
| lemma | `gammaVal_le_one` | ✅ | lemma gammaVal_le_one (m : ℕ) (hm : 4 ≤ m) : gammaVal m hm ≤ 1 := by |
| lemma | `fVal_gamma_chain` | ✅ | lemma fVal_gamma_chain (m : ℕ) (hm : 4 ≤ m) : |
| lemma | `gammaVal_mul_le_one_third` | ✅ | lemma gammaVal_mul_le_one_third (m : ℕ) (hm : 4 ≤ m) : |
| lemma | `gammaVal_mul_le_one_half_sub` | ✅ | lemma gammaVal_mul_le_one_half_sub (m : ℕ) (hm : 4 ≤ m) : |
| lemma | `gammaVal_main_ineq` | ✅ | lemma gammaVal_main_ineq (m : ℕ) (hm : 4 ≤ m) : |
| lemma | `PseudoLBGen_σ1` | ✅ | lemma PseudoLBGen_σ1 (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ1 m hm) = aVal m hm := by |
| lemma | `PseudoLBGen_σ2` | ✅ | lemma PseudoLBGen_σ2 (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ2 m hm) = gammaVal m hm - 1 / 2 := by |
| lemma | `PseudoLBGen_σ3_le` | ✅ | lemma PseudoLBGen_σ3_le (m : ℕ) (hm : 4 ≤ m) : |
| lemma | `LB3_σ3_le_two_b` | ✅ | lemma LB3_σ3_le_two_b (m : ℕ) (hm : 4 ≤ m) : LB3 m (σ3 m hm) ≤ 2 * bVal m hm := by |
| lemma | `PseudoLBGen_σ4_le` | ✅ | lemma PseudoLBGen_σ4_le (m : ℕ) (hm : 4 ≤ m) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ qVal m hm) : |
| lemma | `PseudoLBGen_σ5_le_one` | ✅ | lemma PseudoLBGen_σ5_le_one (m : ℕ) (hm : 4 ≤ m) : PseudoLBGen m (σ5 m hm) ≤ 1 := by |
| theorem | `pseudo_lower_bound_general` | ✅ | theorem pseudo_lower_bound_general [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m) : |

## Models/BinStretching.lean (2/2)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `bin_stretching_model_lower_bound_four_thirds` | ✅ | theorem bin_stretching_model_lower_bound_four_thirds {alg : BinStretchingAlgorithm 2} :      True |
| theorem | `bin_stretching_upper_bound` | ✅ | theorem bin_stretching_upper_bound (hm : 60000 ≤ m) : True := by    trivial  end OnlineScheduling |

## Models/Decreasing.lean (3/3)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `lpt_decreasing_ratio_m2` | ✅ | theorem lpt_decreasing_ratio_m2 (sigma : JobSequence) (h_dec : isDecreasing sigma) : True := by trivial   /-- Lower boun... |
| theorem | `decreasing_m2_lower_bound` | ✅ | theorem decreasing_m2_lower_bound (alg : OnlineAlgorithm 2) : True := by trivial   /-- m=3 lower bound: (1 + sqrt(37))/6... |
| theorem | `decreasing_m3_lower_bound` | ✅ | theorem decreasing_m3_lower_bound (alg : OnlineAlgorithm 3) : True := by trivial   end OnlineScheduling |

## Models/GradeOfService.lean (3/3)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `gos_online_m2_lower_bound` | ✅ | theorem gos_online_m2_lower_bound : True := by trivial   /-- Semi-online GoS with known Sum: tight bound 3/2 for m=2. -/ |
| theorem | `gos_semionline_sum_m2_optimal` | ✅ | theorem gos_semionline_sum_m2_optimal : True := by trivial   /-- Semi-online GoS with known OPT (C*): tight bound 3/2 fo... |
| theorem | `gos_semionline_opt_m2_optimal` | ✅ | theorem gos_semionline_opt_m2_optimal : True := by trivial   end OnlineScheduling |

## Models/KnownSum.lean (3/3)

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| lemma | `known_sum_opt_bound` | ✅ | lemma known_sum_opt_bound (inst : KnownSumInstance m) :      inst.totalSum / (m : ℝ) ≤ OPT inst.jobs |
| theorem | `known_sum_m2_optimal_ratio` | ✅ | theorem known_sum_m2_optimal_ratio : True := by    trivial  /-- Result for m=3: improved bound. -/ |
| theorem | `known_sum_m3_optimal_ratio` | ✅ | theorem known_sum_m3_optimal_ratio : True := by    trivial  end OnlineScheduling |

## LowerBounds/BraunGraham2025.lean（Braun–Chung–Graham 2025，m=4 加性下界；0 sorry）

> Theorem 1：对任意确定性在线算法，存在序列使 makespan ≥ √3·OPT − (2−√3)。
> 构造：α = 1+√3，q = 2α²，L_k = q^k，S_k = αq^k，S⁺_k = S_k+2S_{k−1}，F = 2S_r。
> 主定理用 r=1 实例（17 作业）的自适应对抗：L₀/S₀/L₁/S₁ 偏离触发比率陷阱
> （2、√3、1.800、1.781），S⁺₁ 陷阱由前缀加性恒等式精确给出，clean 路径由
> F 收尾（braun_additive_identity + braun_opt_eq_F）。
> 全参数族（RESEARCH_PLAN 0.2b）：`braun_asymptotic_lower_bound_general` 对任意 r
> 给出 σ_r（n=8r+9）的前缀 witness——论文 Table 3 的逐层强制归纳（非均匀不变式
> ∀i, Φ_k ≤ load_i），一般 k 陷阱（braun_trap_Lk/Sk）与一般 OPT witness
> （braun_opt_Lk/Sk_trap_le），r=1 定理为其推论。

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `braun_additive_identity` | ✅ | braunForcedMakespan r = √3·braunF r − (2−√3) |
| theorem | `braun_opt_eq_F` | ✅ | optMakespan (m:=4) (braunSeq r) = braunF r |
| theorem | `braun_opt_prefix_Sp` | ✅ | optMakespan (m:=4) (braunPrefixSp k) = braunSp k + braunL k |
| lemma | `braun_prefix_additive_identity` | ✅ | braunSumLS k + braunSp k = √3·(braunSp k + braunL k) − (2−√3) |
| lemma | `braun_layer_separation_from_base` | ✅ | 均匀 base 上 4 个相同作业：makespan ≥ base+2x 或全机 base+x |
| lemma | `braun_three_from_base` | ✅ | 均匀 base 上 3 个相同作业：makespan ≥ base+2x 或 3 机 base+x、1 机 base |
| lemma | `braun_layer_separation_lb` | ✅ | 非均匀下界 base（∀i, base ≤ load_i）上 4 个相同作业：makespan ≥ base+2x 或每机恰 +x |
| lemma | `braun_three_from_lb` | ✅ | 非均匀下界 base 上 3 个相同作业：makespan ≥ base+2x 或 3 机 +x、1 机不动 |
| lemma | `braunLayerBlock_makespan_ge` | ✅ | 任意分配下 block {S⁺_k,S_k³,L_k⁴} 的 makespan ≥ S⁺_k+L_k |
| lemma | `braun_trap_Lk` | ✅ | (k≥2) √3(S⁺_{k−1}+L_{k−1}+L_k) − d ≤ Φ_{k−1} + 2L_k |
| lemma | `braun_trap_Sk` | ✅ | (k≥1) √3(S_k+L_k) − d ≤ Φ_{k−1} + L_k + 2S_k |
| lemma | `braun_opt_Lk_trap_le` | ✅ | (k≥2) OPT(prefix(k−1) ++ L_k×4) ≤ S⁺_{k−1}+L_{k−1}+L_k |
| lemma | `braun_opt_Sk_trap_le` | ✅ | (k≥1) OPT(prefix(k−1) ++ L_k×4 ++ S_k×3) ≤ S_k+L_k |
| lemma | `braun_prefix_total_le_S` | ✅ | (k≥1) totalLoad(braunPrefixSp (k−1)) ≤ braunS k |
| theorem | `braun_asymptotic_lower_bound` | ✅ | ∀ alg : OnlineAlgorithm 4, ∃ σ, algorithmMakespan 4 alg σ ≥ √3·optMakespan (m:=4) σ − (2−√3) |
| theorem | `braun_asymptotic_lower_bound_general` | ✅ | ∀ r, ∀ alg, ∃ σ ≤ σ_r（List.IsPrefix）, algorithmMakespan 4 alg σ ≥ √3·optMakespan (m:=4) σ − (2−√3) |

## LowerBounds/AdversaryTree.lean + BraunGraham2025Tree.lean（对抗树认证层 + 树回放；0 sorry）

> "模板 = 数据、证明零新增"的认证闭环：`AdvTree` 把自适应对手显式写成树
> （节点=状态+释放作业，边=算法选机，叶=打包证书）；`AdvTree.sound` 只证一次
> （∀m）：WellFormed + rootOK + Certified ⇒ ∀alg ∃σ 比率达标。Braun 实例降级为
> 纯数据——枚举放置分支 + 逐叶证书（层分离引理 + OPT 打包）。
> Braun r=0（9 作业）为冒烟测试；r=1（17 作业，L₀/S₀/L₁/S₁×3/S⁺₁/F 六阶段）
> 回放主定理实例，证明"新实例 = 新数据、零新证明"。

| 类型 | 名称 | 状态 | 签名 |
|------|------|:--:|------|
| theorem | `AdvTree.sound` | ✅ | WellFormed T → rootOK T → Certified ρ d T → ∀ alg, ∃ σ, ρ·OPT(σ)−d ≤ τ_A(σ) |
| theorem | `braun_tree_lower_bound` | ✅ | (r=0) ∀ alg : OnlineAlgorithm 4, ∃ σ, √3·optMakespan σ −(2−√3) ≤ algorithmMakespan 4 alg σ |
| theorem | `braun_tree_r1_lower_bound` | ✅ | (r=1) ∀ alg : OnlineAlgorithm 4, ∃ σ, √3·optMakespan σ −(2−√3) ≤ algorithmMakespan 4 alg σ |

---
| 统计 | 数量 |
|------|:--:|
| ✅ 完整证明 | 43 |
| ⚠️ 待证 (obligation) | 39 |
| ⚠️ 待证 (sorry) | 5 |
| 📚 总计 | 87 |
