/-
P6||Cmax with Known Total Sum: Lower Bound 3/2

Adaptive adversary:
1. Send m jobs of size 3/4 (m ≥ 6).
   - Imbalanced → ratio ≥ 2 > 3/2 (via Faigle.layer_separation).
   - Balanced (all = 3/4) → send [3/2].
     makespan ≥ 3/4+3/2 = 9/4, OPT = 3/2, ratio = 3/2.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset

namespace OnlineScheduling

theorem ks6_lower_bound_three_halves (m : Nat) [NeZero m] (hm : 6 ≤ m)
    (alg : OnlineAlgorithm m) :
    ∃ sigma : JobSequence,
      algorithmMakespan m alg sigma ≥ (3 / 2 : ℝ) * OPT sigma := by
  have hm_rat : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos_rat' : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  set x := (3 / 4 : ℝ) with hx
  have hxpos : 0 < x := by norm_num

  -- Phase 1: m jobs of size 3/4
  have h_layer1 := layer_separation (m := m) alg x hxpos
  rcases h_layer1 with (h_imbal | h_bal)
  · -- Imbalanced: ratio ≥ 2 > 3/2
    use List.replicate m x
    have h_opt1 : OPT (List.replicate m x) = x :=
      opt_of_identical_jobs (m := m) x hxpos
    rw [h_opt1] at h_imbal
    have h_two_gt_three_halves : (2 : ℝ) * x > (3/2 : ℝ) * x := by nlinarith
    nlinarith

  · -- Balanced: all loads = 3/4
    let sigma := List.replicate m x ++ [3/2]
    use sigma
    let loads1 := runAlgorithm m alg (List.replicate m x)
    have h_loads1 : ∀ i, loads1 i = x := h_bal

    -- After [3/2]: receiving machine gets x + 3/2 = 3/4 + 3/2 = 9/4
    let j := alg loads1 (3/2 : ℝ)
    have h_load_j : runAlgorithm m alg sigma j = x + 3/2 := by
      have h_run : runAlgorithm m alg sigma = step (m := m) alg loads1 (3/2 : ℝ) := by
        simp [sigma, runAlgorithm, loads1]
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1 j]
      · exfalso
        exact hif rfl

    have h_makespan_ge : x + 3/2 ≤ algorithmMakespan m alg sigma := by
      dsimp [algorithmMakespan]
      have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) j
      rw [h_load_j] at h; exact h

    -- OPT = 3/2
    have h_total : totalLoad sigma = (m : ℝ) * x + 3/2 := by
      simp [totalLoad, sigma, nsmul_eq_mul]

    have h_opt_eq : OPT sigma = (3/2 : ℝ) := by
      apply le_antisymm
      · -- OPT ≤ 3/2 via uniform schedule: M0=3/2, others share remaining
        let sched (i : Fin m) : ℝ :=
          if i = (0 : Fin m) then (3/2 : ℝ) else (m * x) / ((m : ℝ) - 1)
        have h_sum : totalLoad sigma = (∑ i : Fin m, sched i) := by
          have hsum_sched : (∑ i : Fin m, sched i) = (3 / 2 : ℝ) + (m : ℝ) * x := by
            have hsplit : (∑ i : Fin m, sched i) =
                (∑ i : Fin m, (if i = (0 : Fin m) then (3 / 2 : ℝ) else 0)) +
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
        have h_makespan_sched : makespan m sched = (3/2 : ℝ) := by
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
        rw [h_makespan_sched] at h_opt_sched; exact h_opt_sched
      · -- OPT ≥ 3/2: max job = 3/2
        have h_max : maxJobSize sigma = (3/2 : ℝ) := by
          apply le_antisymm
          · rw [maxJobSize]
            have hle_each : ∀ p ∈ (List.replicate m x ++ [3/2]), p ≤ (3/2 : ℝ) := by
              intro p hp
              rw [List.mem_append] at hp
              rcases hp with hp | hp
              · rw [List.mem_replicate] at hp
                rcases hp with ⟨_, hpeq⟩
                rw [hpeq, hx]
                norm_num
              · simp at hp
                rw [← hp]
            have hfold : ∀ (l : List ℝ) (b : ℝ), b ≤ (3/2 : ℝ) →
                (∀ p ∈ l, p ≤ (3/2 : ℝ)) → l.foldl max b ≤ (3/2 : ℝ) := by
              intro l
              induction l with
              | nil => intro b hb _; simpa [List.foldl]
              | cons a l ih =>
                  intro b hb hle
                  simp [List.foldl]
                  exact ih (max b a) (max_le hb (hle a (by simp)))
                    (fun p hp => hle p (by simp [hp]))
            exact hfold (List.replicate m x ++ [3/2]) 0 (by norm_num) hle_each
          · have h := maxJobSize_ge_each sigma (3/2 : ℝ)
            have hmem : (3/2 : ℝ) ∈ sigma := by
              simp [sigma]
            exact h hmem
        have h := opt_ge_max_job sigma
        simpa [h_max] using h

    rw [h_opt_eq]
    -- makespan ≥ x + 3/2 = 3/4 + 3/2 = 9/4 = (3/2) * (3/2)
    -- So ratio ≥ (9/4) / (3/2) = 3/2
    have h' : (3 / 2 : ℝ) * (3 / 2) ≤ x + 3 / 2 := by
      rw [hx]
      norm_num
    nlinarith

end OnlineScheduling
