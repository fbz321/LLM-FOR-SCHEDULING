/-
Bin-Stretching Lower Bound: 4/3 (Azar & Regev, 2001)

Adaptive adversary:
1. Send m jobs of size 1/3.
   - Imbalanced → ratio ≥ 2 > 4/3 (via Faigle.layer_separation).
   - Balanced (all = 1/3) → send [1].
     makespan ≥ 1/3+1 = 4/3, OPT = 1, ratio = 4/3.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset

namespace OnlineScheduling

theorem bin_stretching_lower_bound_four_thirds (m : Nat) [NeZero m]
    (hm : 2 < m) (alg : OnlineAlgorithm m) :
    ∃ sigma : JobSequence,
      algorithmMakespan m alg sigma ≥ (4 / 3 : ℝ) * OPT sigma := by
  have hm_rat : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
  have hm_pos_rat' : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  set x := (1 / 3 : ℝ) with hx
  have hxpos : 0 < x := by norm_num
  let σ₁ := List.replicate m x

  -- Phase 1: m jobs of size x = 1/3 → either imbalanced or balanced
  have h_layer1 := layer_separation (m := m) alg x hxpos
  rcases h_layer1 with (h_imbal | h_bal)
  · -- Imbalanced: ratio ≥ 2*OPT = 2x, and 2x > (4/3)*x
    use σ₁
    have h_opt1 : OPT σ₁ = x := opt_of_identical_jobs (m := m) x hxpos
    rw [h_opt1] at h_imbal
    nlinarith

  · -- Balanced: all loads = x
    let sigma := σ₁ ++ [1]
    use sigma
    let loads₁ := runAlgorithm m alg σ₁
    have h_loads1 : ∀ i : Fin m, loads₁ i = x := h_bal

    -- After [1], the receiving machine gets x+1 = 4/3
    let j := alg loads₁ (1 : ℝ)
    have h_load_j : runAlgorithm m alg sigma j = x + 1 := by
      have h_run : runAlgorithm m alg sigma = step (m := m) alg loads₁ (1 : ℝ) := by
        simp [sigma, σ₁, runAlgorithm, loads₁]
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1 j]
      · exfalso
        exact hif rfl

    have h_makespan_ge : x + 1 ≤ algorithmMakespan m alg sigma := by
      dsimp [algorithmMakespan]
      have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) j
      rw [h_load_j] at h; exact h

    -- OPT = 1
    have h_total : totalLoad sigma = (m : ℝ) * x + 1 := by
      simp [totalLoad, sigma, σ₁, nsmul_eq_mul]

    have h_opt_le_one : OPT sigma ≤ (1 : ℝ) := by
      -- Uniform fractional schedule: M0 = 1, others = m·x/(m-1)
      let sched (i : Fin m) : ℝ :=
        if i = (0 : Fin m) then (1 : ℝ) else (m : ℝ) * x / ((m : ℝ) - 1)
      have h_sum : totalLoad sigma = (∑ i : Fin m, sched i) := by
        have hsum_sched : (∑ i : Fin m, sched i) = (1 : ℝ) + (m : ℝ) * x := by
          have hsplit : (∑ i : Fin m, sched i) =
              (∑ i : Fin m, (if i = (0 : Fin m) then (1 : ℝ) else 0)) +
              (∑ i : Fin m, (if i = (0 : Fin m) then 0 else (m : ℝ) * x / ((m : ℝ) - 1))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            dsimp [sched]
            by_cases h : i = (0 : Fin m) <;> simp [h]
          rw [hsplit]
          simp [Finset.sum_ite_eq]
          congr 1
          rw [show (∑ i : Fin m, (if i = (0 : Fin m) then 0 else (m : ℝ) * x / ((m : ℝ) - 1))) =
              (∑ i : Fin m, (if i ≠ (0 : Fin m) then (m : ℝ) * x / ((m : ℝ) - 1) else 0)) by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases h : i = (0 : Fin m) <;> simp [h]]
          rw [← Finset.sum_filter]
          have hcard : (Finset.univ.filter (fun i : Fin m => i ≠ (0 : Fin m))).card = m - 1 := by
            rw [Finset.filter_ne']
            rw [Finset.card_erase_of_mem (by simp : (0 : Fin m) ∈ (Finset.univ : Finset (Fin m)))]
            rw [Finset.card_univ, Fintype.card_fin]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [hcard]
          rw [Nat.cast_sub (by exact Nat.succ_le_of_lt (Nat.pos_of_neZero m))]
          have hm1 : (m : ℝ) - 1 ≠ 0 := by nlinarith [hm_rat]
          field_simp [hm1]
          ring
        rw [h_total, hsum_sched]
        ring
      have h_makespan_sched : makespan m sched = (1 : ℝ) := by
        apply le_antisymm
        · dsimp [makespan]
          exact Finset.sup'_le Finset.univ_nonempty sched (by
            intro i hi
            dsimp [sched]
            split_ifs with hif
            · simp
            · rw [hx]
              have hm1 : (m : ℝ) - 1 ≠ 0 := by nlinarith [hm_rat]
              have hm1_pos : 0 < (m : ℝ) - 1 := by nlinarith [hm_rat]
              field_simp [hm1]
              nlinarith [hm_rat, hm1_pos])
        · have h := makespan_ge_each (m := m) sched (0 : Fin m)
          simpa [sched] using h
      have h_opt_sched := opt_le_of_schedule (m := m) sigma sched h_sum
      rw [h_makespan_sched] at h_opt_sched
      exact h_opt_sched

    have h_opt_ge_one : (1 : ℝ) ≤ OPT sigma := by
      have h_max : maxJobSize sigma = (1 : ℝ) := by
        apply le_antisymm
        · rw [maxJobSize]
          have hle_each : ∀ p ∈ (List.replicate m x ++ [1]), p ≤ (1 : ℝ) := by
            intro p hp
            rw [List.mem_append] at hp
            rcases hp with hp | hp
            · rw [List.mem_replicate] at hp
              rcases hp with ⟨_, hpeq⟩
              rw [hpeq, hx]
              norm_num
            · simp at hp
              rw [← hp]
          have hfold : ∀ (l : List ℝ) (b : ℝ), b ≤ (1 : ℝ) →
              (∀ p ∈ l, p ≤ (1 : ℝ)) → l.foldl max b ≤ (1 : ℝ) := by
            intro l
            induction l with
            | nil => intro b hb _; simpa [List.foldl]
            | cons a l ih =>
                intro b hb hle
                simp [List.foldl]
                exact ih (max b a) (max_le hb (hle a (by simp)))
                  (fun p hp => hle p (by simp [hp]))
          exact hfold (List.replicate m x ++ [1]) 0 (by norm_num) hle_each
        · have h := maxJobSize_ge_each sigma (1 : ℝ)
          have hmem : (1 : ℝ) ∈ sigma := by
            simp [sigma, σ₁]
          exact h hmem
      have h := opt_ge_max_job sigma
      simpa [h_max] using h

    have h_opt_eq_one : OPT sigma = (1 : ℝ) := le_antisymm h_opt_le_one h_opt_ge_one

    rw [h_opt_eq_one]
    have h' : (4 / 3 : ℝ) ≤ x + 1 := by
      rw [hx]
      norm_num
    simpa using (le_trans h' h_makespan_ge)

end OnlineScheduling
