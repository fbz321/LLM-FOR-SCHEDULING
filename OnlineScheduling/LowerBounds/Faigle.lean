/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Faigle-Kern-Turan Lower Bound: `1 + sqrt(2)/2 ≈ 1.707`

Adaptive adversary:
1. Send m jobs of size `a = √2/2 - 1/2`.
   - If some machine gets ≥ 2a → makespan ≥ 2a, OPT = a, ratio ≥ 2 > fkt.
   - Otherwise all machines have load `a` → continue.
2. Send m jobs of size `b = 1/2`.
   - If some machine gets ≥ a+2b → ratio = (a+2b)/(a+b) = 1+1/√2 = fkt.
   - Otherwise all machines have load `a+b = √2/2` → continue.
3. Send final job `1` → makespan ≥ √2/2 + 1.
   OPT ≤ √2/2 + 1/m (uniform schedule), ratio ≥ fkt for m ≥ 4.
-/

import OnlineScheduling.Basic

open Finset

namespace OnlineScheduling

noncomputable def fkt_constant : ℝ := 1 + Real.sqrt 2 / 2

noncomputable def fkt_a : ℝ := Real.sqrt 2 / 2 - 1 / 2
noncomputable def fkt_b : ℝ := 1 / 2

lemma fkt_a_pos : 0 < fkt_a := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  dsimp [fkt_a]
  nlinarith

lemma fkt_b_pos : 0 < fkt_b := by norm_num [fkt_b]

lemma fkt_a_add_b : fkt_a + fkt_b = Real.sqrt 2 / 2 := by dsimp [fkt_a, fkt_b]; ring

lemma fkt_ratio_eq : (fkt_a + 2 * fkt_b) / (fkt_a + fkt_b) = fkt_constant := by
  rw [fkt_a_add_b]
  have h_add : fkt_a + 2 * fkt_b = Real.sqrt 2 / 2 + 1 / 2 := by dsimp [fkt_a, fkt_b]; ring
  rw [h_add, fkt_constant]
  have h_ne : Real.sqrt 2 / 2 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [h_ne]
  nlinarith [hsq]

/-! ### Helper: loads after identical jobs are multiples of the job size -/

private lemma loads_are_multiples_aux {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) :
    ∀ (t : ℕ) (loads_start : Loads m) (h_start : ∀ i, ∃ k : ℕ, loads_start i = (k : ℝ) * x),
    ∀ i : Fin m, ∃ k : ℕ,
      ((List.replicate t x).foldl (step (m := m) alg) loads_start) i = (k : ℝ) * x := by
  intro t
  induction t with
  | zero =>
      intro loads_start h_start i
      exact h_start i
  | succ t ih =>
      intro loads_start h_start i
      have h_acc : ∀ j : Fin m, ∃ k : ℕ, (step (m := m) alg loads_start x) j = (k : ℝ) * x := by
        intro j
        dsimp [step]
        rcases h_start j with ⟨k, hk⟩
        split_ifs
        · simp [hk]
          exact ⟨k + 1, by push_cast; ring⟩
        · simp [hk]
      have h_final := ih (step (m := m) alg loads_start x) h_acc i
      simpa [List.replicate_succ, List.foldl_cons] using h_final

lemma loads_are_multiples' {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (t : ℕ)
    (loads_start : Loads m) (h_start : ∀ i, ∃ k : ℕ, loads_start i = (k : ℝ) * x) (i : Fin m) :
    ∃ k : ℕ, ((List.replicate t x).foldl (step (m := m) alg) loads_start) i = (k : ℝ) * x :=
  loads_are_multiples_aux alg x t loads_start h_start i

lemma loads_are_multiples_from_zero {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (t : ℕ)
    (i : Fin m) : ∃ k : ℕ, runAlgorithm m alg (List.replicate t x) i = (k : ℝ) * x := by
  simpa [runAlgorithm] using
    loads_are_multiples_aux alg x t (λ _ => 0) (by intro i; exact ⟨0, by simp⟩) i

/-! ### Lemma: OPT of m identical jobs equals the job size -/

lemma opt_of_identical_jobs {m : ℕ} [NeZero m] (x : ℝ) (hxpos : 0 < x) :
    OPT (List.replicate m x) = x := by
  apply le_antisymm
  · have h_mk : makespan m (λ _ => x) = x := by
      apply le_antisymm
      · dsimp [makespan]
        exact Finset.sup'_le Finset.univ_nonempty (fun _ => x) (by intro i hi; simp)
      · have h := makespan_ge_each (m := m) (λ _ => x) 0
        simpa using h
    have h_total : totalLoad (List.replicate m x) = ∑ i : Fin m, x := by
      simp [totalLoad]
    exact le_trans (opt_le_of_schedule (m := m) (List.replicate m x) (λ _ => x) h_total)
      (by rw [h_mk])
  · have h_avg : totalLoad (List.replicate m x) / (m : ℝ) = x := by
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
      simp [totalLoad]
      field_simp [hm_ne]
    have h := opt_ge_avg_load (m := m) (List.replicate m x)
    rwa [h_avg] at h

/-! ### Lemma: layer separation — either ratio ≥ 2 or perfectly balanced -/

lemma layer_separation {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (hxpos : 0 < x) :
    let σ := List.replicate m x
    algorithmMakespan m alg σ ≥ 2 * OPT σ
    ∨ (∀ i : Fin m, runAlgorithm m alg σ i = x) := by
  intro σ
  have h_total : (∑ i : Fin m, runAlgorithm m alg σ i) = (m : ℝ) * x := by
    rw [runAlgorithm_total_load (m := m) alg σ]
    simp [σ, totalLoad]
  have h_opt_eq : OPT σ = x := opt_of_identical_jobs (m := m) x hxpos

  by_cases h_exists : ∃ i : Fin m, (2 : ℝ) * x ≤ runAlgorithm m alg σ i
  · left
    rcases h_exists with ⟨i, hi⟩
    have h_makespan_ge : 2 * x ≤ algorithmMakespan m alg σ := by
      dsimp [algorithmMakespan]
      have h := makespan_ge_each (m := m) (runAlgorithm m alg σ) i
      linarith
    rw [h_opt_eq]
    exact h_makespan_ge
  · right
    push_neg at h_exists
    -- Each load is k_i·x with k_i ∈ ℕ; since load < 2x, k_i ≤ 1
    choose n hn using loads_are_multiples_from_zero (m := m) alg x m
    -- The sum of loads equals m·x; factor out x to get Σ (n i) = m
    have h_sum_n_real : (∑ i : Fin m, (n i : ℝ) * x) = (m : ℝ) * x := by
      calc
        (∑ i : Fin m, (n i : ℝ) * x) = (∑ i : Fin m, runAlgorithm m alg σ i) :=
          Finset.sum_congr rfl (λ i hi => by rw [hn i])
        _ = (m : ℝ) * x := h_total
    have h_sum_n : (∑ i : Fin m, (n i : ℕ)) = m := by
      have h_cast_sum : (∑ i : Fin m, ((n i : ℕ) : ℝ)) = (m : ℝ) := by
        have h' : (∑ i : Fin m, ((n i : ℕ) : ℝ)) * x = (m : ℝ) * x := by
          simpa [Finset.sum_mul] using h_sum_n_real
        exact mul_right_cancel₀ (ne_of_gt hxpos) h'
      exact_mod_cast h_cast_sum
    -- Each n_i < 2 → n_i ≤ 1
    have hn_le_one : ∀ i, n i ≤ 1 := by
      intro i
      have h_load_lt : runAlgorithm m alg σ i < (2 : ℝ) * x := h_exists i
      rw [hn i] at h_load_lt
      have hn_real_lt_two : (n i : ℝ) < 2 := by nlinarith
      have hn_nat_lt_two : n i < 2 := by exact_mod_cast hn_real_lt_two
      omega
    -- Pigeonhole: m terms, each ≤ 1, sum = m → all equal 1
    have hn_all_one : ∀ i, n i = 1 := by
      intro i
      exact pigeonhole_all_ones (m := m) n hn_le_one h_sum_n i
    intro i
    rw [hn i, hn_all_one i, Nat.cast_one, one_mul]

/-! ### Helper: loads from base are base + integer multiples of job size -/

private lemma loads_are_multiples_from_base {m : ℕ} [NeZero m]
    (alg : OnlineAlgorithm m) (base x : ℝ) :
    ∀ (t : ℕ) (loads_start : Loads m)
      (h_start : ∀ i, ∃ k : ℕ, loads_start i = base + (k : ℝ) * x),
    ∀ i : Fin m, ∃ k : ℕ,
      ((List.replicate t x).foldl (step (m := m) alg) loads_start) i = base + (k : ℝ) * x := by
  intro t
  induction t with
  | zero =>
      intro loads_start h_start i
      exact h_start i
  | succ t ih =>
      intro loads_start h_start i
      have h_acc :
          ∀ j : Fin m, ∃ k : ℕ, (step (m := m) alg loads_start x) j = base + (k : ℝ) * x := by
        intro j
        dsimp [step]
        rcases h_start j with ⟨k, hk⟩
        split_ifs
        · simp [hk]
          exact ⟨k + 1, by push_cast; ring⟩
        · simp [hk]
      have h_final := ih (step (m := m) alg loads_start x) h_acc i
      simpa [List.replicate_succ, List.foldl_cons] using h_final

/-! ### Lemma: layer separation from a uniform base load -/

lemma layer_separation_from_base {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m)
    (base x : ℝ) (hxpos : 0 < x)
    (loads_before : Loads m) (h_uniform : ∀ i : Fin m, loads_before i = base) :
    let tau := List.replicate m x
    let loads_after := tau.foldl (step (m := m) alg) loads_before
    makespan m loads_after ≥ base + 2 * x
    ∨ (∀ i : Fin m, loads_after i = base + x) := by
  intro tau loads_after
  have h_total_after : (∑ i : Fin m, loads_after i) = (m : ℝ) * (base + x) := by
    rw [show loads_after = tau.foldl (step (m := m) alg) loads_before from rfl]
    rw [sum_foldl_step (m := m) alg loads_before tau]
    have h_sum_before : (∑ i : Fin m, loads_before i) = (m : ℝ) * base := by
      simp [h_uniform]
    rw [h_sum_before]
    simp [tau, totalLoad]
    ring

  -- Each loads_after i = base + k_i·x for some k_i ∈ ℕ
  choose n hn using loads_are_multiples_from_base (m := m) alg base x m
    loads_before (by intro i; rw [h_uniform i]; exact ⟨0, by simp⟩)

  -- Sum: Σ (base + n_i·x) = m·(base+x) → m·base + Σ n_i·x = m·base + m·x → Σ n_i = m
  have h_sum_n_real : (∑ i : Fin m, (n i : ℝ) * x) = (m : ℝ) * x := by
    have h_all : (∑ i : Fin m, (base + (n i : ℝ) * x)) = (m : ℝ) * (base + x) := by
      calc
        (∑ i : Fin m, (base + (n i : ℝ) * x)) = (∑ i : Fin m, loads_after i) :=
          Finset.sum_congr rfl (λ i hi => by
            change base + (n i : ℝ) * x =
              ((List.replicate m x).foldl (step (m := m) alg) loads_before) i
            exact (hn i).symm)
        _ = (m : ℝ) * (base + x) := h_total_after
    -- Expand LHS and RHS
    have h_expand : (∑ i : Fin m, (base + (n i : ℝ) * x)) =
        (m : ℝ) * base + (∑ i : Fin m, (n i : ℝ) * x) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand] at h_all
    nlinarith

  have h_sum_n : (∑ i : Fin m, (n i : ℕ)) = m := by
    have h_cast_sum : (∑ i : Fin m, ((n i : ℕ) : ℝ)) = (m : ℝ) := by
      have h' : (∑ i : Fin m, ((n i : ℕ) : ℝ)) * x = (m : ℝ) * x := by
        simpa [Finset.sum_mul] using h_sum_n_real
      exact mul_right_cancel₀ (ne_of_gt hxpos) h'
    exact_mod_cast h_cast_sum

  -- If some n_i ≥ 2: load ≥ base + 2x
  by_cases h_exists : ∃ i, 2 ≤ n i
  · left
    rcases h_exists with ⟨i, hi⟩
    have h_load_ge : base + 2 * x ≤ loads_after i := by
      change base + 2 * x ≤
        ((List.replicate m x).foldl (step (m := m) alg) loads_before) i
      rw [hn i]
      have : (2 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hi
      nlinarith
    have h_makespan_ge : base + 2 * x ≤ makespan m loads_after := by
      have h := makespan_ge_each (m := m) loads_after i
      linarith
    exact h_makespan_ge
  · -- All n_i ≤ 1, and Σ n_i = m → all n_i = 1
    right
    push_neg at h_exists
    have hn_le_one : ∀ i, n i ≤ 1 := by
      intro i; have h := h_exists i; omega
    have hn_all_one : ∀ i, n i = 1 := by
      intro i
      exact pigeonhole_all_ones (m := m) n hn_le_one h_sum_n i
    intro i
    change ((List.replicate m x).foldl (step (m := m) alg) loads_before) i = base + x
    rw [hn i, hn_all_one i, Nat.cast_one, one_mul]

/-! ### Main theorem -/

theorem faigle_kern_turan_lower_bound [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m) :
    ∃ (sigma : JobSequence),
    algorithmMakespan m alg sigma ≥ fkt_constant * OPT sigma := by
  have hm_rat : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos_rat' : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)

  set a := fkt_a
  set b := fkt_b
  have ha_pos : 0 < a := fkt_a_pos
  have hb_pos : 0 < b := fkt_b_pos
  have hab : a + b = Real.sqrt 2 / 2 := fkt_a_add_b

  -- Phase 1: m jobs of size a
  let σ₁ := List.replicate m a
  have h_layer1 := layer_separation (m := m) alg a ha_pos
  rcases h_layer1 with (h_imbal1 | h_bal1)
  · -- Imbalanced: ratio ≥ 2 > fkt_constant
    use σ₁
    have h_opt1 : OPT σ₁ = a := opt_of_identical_jobs (m := m) a ha_pos
    rw [h_opt1] at h_imbal1
    have h_two_gt_fkt : (2 : ℝ) > fkt_constant := by
      dsimp [fkt_constant]
      have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    nlinarith

  · -- Balanced after a-layer: all loads = a
    -- Phase 2: m jobs of size b on top of base a
    let τ := List.replicate m b
    let loads₁ := runAlgorithm m alg σ₁
    have h_loads1_eq : ∀ i : Fin m, loads₁ i = a := h_bal1
    have h_loads1_sum : (∑ i : Fin m, loads₁ i) = (m : ℝ) * a := by simp [h_loads1_eq]
    let loads₂ := τ.foldl (step (m := m) alg) loads₁
    let σ₂ := σ₁ ++ τ

    have h_run2 : runAlgorithm m alg σ₂ = loads₂ := by
      simp [σ₂, σ₁, τ, loads₁, loads₂, runAlgorithm]

    have h_layer2 := layer_separation_from_base (m := m) alg a b hb_pos
      loads₁ h_loads1_eq
    rcases h_layer2 with (h_imbal2 | h_bal2)

    · -- Imbalanced after b-layer: makespan ≥ a + 2b
      use σ₂
      have h_opt2 : OPT σ₂ = a + b := by
        apply le_antisymm
        · have h_mk : makespan m (λ _ => a + b) = a + b := by
            apply le_antisymm
            · dsimp [makespan]
              exact Finset.sup'_le Finset.univ_nonempty (fun _ => a + b) (by intro i hi; simp)
            · have h := makespan_ge_each (m := m) (λ _ => a + b) 0
              simpa using h
          have h_total2 : totalLoad σ₂ = ∑ i : Fin m, (a + b) := by
            simp [totalLoad, σ₂, σ₁, τ]
          exact le_trans (opt_le_of_schedule (m := m) σ₂ (λ _ => a + b) h_total2)
            (by rw [h_mk])
        · have h_avg : (totalLoad σ₂) / (m : ℝ) = a + b := by
            simp [totalLoad, σ₂, σ₁, τ]
            field_simp [hm_pos_rat']
          have h := opt_ge_avg_load (m := m) σ₂
          rwa [h_avg] at h
      have h_makespan_ge : a + 2 * b ≤ algorithmMakespan m alg σ₂ := by
        dsimp [algorithmMakespan]
        rw [h_run2]
        exact h_imbal2
      calc
        algorithmMakespan m alg σ₂ ≥ a + 2 * b := h_makespan_ge
        _ = ((a + 2 * b) / (a + b)) * (a + b) := by
          field_simp [show a + b ≠ 0 from by nlinarith]
        _ = ((a + 2 * b) / (a + b)) * OPT σ₂ := by rw [h_opt2]
        _ = fkt_constant * OPT σ₂ := by rw [fkt_ratio_eq]

    · -- Balanced after both layers: all loads = a+b = √2/2
      -- Phase 3: final job of size 1
      let σ₃ := σ₂ ++ [1]
      use σ₃

      have h_run3 : runAlgorithm m alg σ₃ =
          step (m := m) alg loads₂ (1 : ℝ) := by
        simp [σ₃, σ₂, σ₁, τ, loads₁, loads₂, runAlgorithm]

      -- After σ₂, all loads = a+b (from h_bal2, since loads₂ = τ.foldl ... loads₁)
      have h_loads2 : ∀ i : Fin m, loads₂ i = a + b := h_bal2

      -- After [1], the receiving machine gets load a+b+1
      let j := alg loads₂ (1 : ℝ)
      have h_load_j : runAlgorithm m alg σ₃ j = a + b + 1 := by
        rw [h_run3]; dsimp [step]; simp [h_loads2 j, j]

      have h_makespan_ge : a + b + 1 ≤ algorithmMakespan m alg σ₃ := by
        dsimp [algorithmMakespan]
        have h := makespan_ge_each (m := m) (runAlgorithm m alg σ₃) j
        rw [h_load_j] at h; exact h

      -- OPT upper bound via uniform schedule: each machine load = (a+b) + 1/m
      have h_total3 : totalLoad σ₃ = (m : ℝ) * (a + b) + 1 := by
        simp [totalLoad, σ₃, σ₂, σ₁, τ, nsmul_eq_mul]
        ring

      have h_opt_le : OPT σ₃ ≤ (a + b) + 1 / (m : ℝ) := by
        have h_schedule_sum : totalLoad σ₃ =
            (∑ i : Fin m, ((a + b) + 1 / (m : ℝ))) := by
          rw [h_total3]
          simp [nsmul_eq_mul]
          field_simp [hm_pos_rat']
        have h_schedule_makespan : makespan m (λ _ => (a + b) + 1 / (m : ℝ))
            = (a + b) + 1 / (m : ℝ) := by
          apply le_antisymm
          · dsimp [makespan]
            exact Finset.sup'_le Finset.univ_nonempty (fun _ => (a + b) + 1 / (m : ℝ))
              (by intro i hi; simp)
          · have h := makespan_ge_each (m := m) (λ _ => (a + b) + 1 / (m : ℝ)) 0
            simpa using h
        exact le_trans
          (opt_le_of_schedule (m := m) σ₃ (λ _ => (a + b) + 1 / (m : ℝ)) h_schedule_sum)
          (by rw [h_schedule_makespan])

      -- Ratio: (a+b+1) / (a+b+1/m) ≥ fkt_constant for m ≥ 4
      have h_ratio : fkt_constant * ((a + b) + 1 / (m : ℝ)) ≤ a + b + 1 := by
        rw [hab]
        dsimp [fkt_constant]
        have h_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
          calc
            Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
            _ = 2 := Real.sq_sqrt (show 0 ≤ 2 from by norm_num)
        have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h_two_le_m : 2 * (1 + Real.sqrt 2 / 2) ≤ (m : ℝ) := by
          nlinarith [h_sq, hnn, hm_rat]
        have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (NeZero.pos m)
        field_simp [hm_pos.ne']
        ring_nf
        have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        nlinarith [h_sq, h_two_le_m]

      have hfkt_nonneg : 0 ≤ fkt_constant := by
        dsimp [fkt_constant]
        nlinarith [Real.sqrt_nonneg 2]
      nlinarith [hfkt_nonneg]

end OnlineScheduling
