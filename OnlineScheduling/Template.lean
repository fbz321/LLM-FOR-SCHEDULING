import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Lemmas

open OnlineScheduling

set_option maxHeartbeats 400000

/-
Verified 2-layer adversary template.
Given job sizes a1, a2, F and a target ratio rho, if the three numeric
hypotheses hold, the adversary works.
-/
theorem template_2layer {m : Nat} [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m)
    (a1 a2 F rho : ℝ) (ha1pos : 0 < a1) (ha2pos : 0 < a2) (hFpos : 0 < F)
    (hrho_nonneg : 0 ≤ rho) (h_two_gt_rho : (2 : ℝ) > rho)
    (h_imbal2_ratio : a1 + 2 * a2 ≥ rho * (a1 + a2))
    (h_final_ratio : a1 + a2 + F ≥ rho * (a1 + a2 + F / (m : ℝ))) :
    ∃ σ : JobSequence, rho * OPT σ ≤ algorithmMakespan m alg σ := by
  let sigma1 : JobSequence := List.replicate m a1
  have h_p1 := layer_separation (m := m) alg a1 ha1pos
  rcases h_p1 with h_imbal1 | h_bal1
  · use sigma1
    have h_opt_nonneg : 0 ≤ OPT sigma1 := by
      have h_max_nonneg : 0 ≤ maxJobSize sigma1 := by
        refine maxJobSize_nonneg sigma1 ?_
        intro p hp
        have hp' : p = a1 := (List.mem_replicate.mp hp).2
        simpa [sigma1, hp'] using ha1pos.le
      exact le_trans h_max_nonneg (opt_ge_max_job sigma1)
    calc
      rho * OPT sigma1 ≤ (2 : ℝ) * OPT sigma1 := by
        nlinarith
      _ ≤ algorithmMakespan m alg sigma1 := h_imbal1
  · have h_loads1 : ∀ i : Fin m, runAlgorithm m alg sigma1 i = a1 := h_bal1
    let loads1 : Loads m := runAlgorithm m alg sigma1
    let tau2 : JobSequence := List.replicate m a2
    let sigma2 : JobSequence := sigma1 ++ tau2
    have h_p2 := layer_separation_from_base (m := m) alg a1 a2 ha2pos loads1 h_loads1
    rcases h_p2 with h_imbal2 | h_bal2
    · use sigma2
      have h_sched : totalLoad sigma2 = ∑ i : Fin m, ((fun _ : Fin m => a1 + a2) i) := by
        dsimp [sigma2, sigma1, tau2, totalLoad]
        simp [List.sum_append, List.sum_replicate]
      have h_mk_uni : makespan m (fun _ : Fin m => a1 + a2) = a1 + a2 := by
        apply le_antisymm
        · have h_univ_nonempty : Finset.Nonempty (Finset.univ : Finset (Fin m)) := Finset.univ_nonempty
          exact Finset.sup'_le h_univ_nonempty (fun _ : Fin m => a1 + a2)
            (by intro i hi; simp)
        · have h := makespan_ge_each (m := m) (fun _ : Fin m => a1 + a2) (0 : Fin m)
          simpa using h
      have h_opt : OPT sigma2 ≤ a1 + a2 := by
        have h_le := opt_le_of_schedule (m := m) sigma2 (fun _ : Fin m => a1 + a2) h_sched
        rw [h_mk_uni] at h_le
        exact h_le
      have h_alg_mk : a1 + 2 * a2 ≤ algorithmMakespan m alg sigma2 := by
        simpa [algorithmMakespan, sigma2, sigma1, tau2, loads1, runAlgorithm, List.foldl_append]
          using h_imbal2
      calc
        rho * OPT sigma2 ≤ rho * (a1 + a2) := by
          exact mul_le_mul_of_nonneg_left h_opt hrho_nonneg
        _ ≤ a1 + 2 * a2 := h_imbal2_ratio
        _ ≤ algorithmMakespan m alg sigma2 := h_alg_mk
    · set loads2 : Loads m := tau2.foldl (step (m := m) alg) loads1 with h_loads2_def
      have h_loads2 : ∀ i : Fin m, loads2 i = a1 + a2 := by
        simpa [loads2] using h_bal2
      let sigma3 : JobSequence := sigma2 ++ [F]
      use sigma3
      have h_sched : totalLoad sigma3 = ∑ i : Fin m, ((fun _ : Fin m => a1 + a2 + F / (m : ℝ)) i) := by
        dsimp [sigma3, sigma2, sigma1, tau2, totalLoad]
        simp [List.sum_append, List.sum_replicate]
        have h_div : F = (m : ℝ) * (F / (m : ℝ)) := by
          field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast NeZero.ne m]
        nlinarith [h_div]
      have h_mk_uni : makespan m (fun _ : Fin m => a1 + a2 + F / (m : ℝ)) = a1 + a2 + F / (m : ℝ) := by
        apply le_antisymm
        · have h_univ_nonempty : Finset.Nonempty (Finset.univ : Finset (Fin m)) := Finset.univ_nonempty
          exact Finset.sup'_le h_univ_nonempty (fun _ : Fin m => a1 + a2 + F / (m : ℝ))
            (by intro i hi; simp)
        · have h := makespan_ge_each (m := m) (fun _ : Fin m => a1 + a2 + F / (m : ℝ)) (0 : Fin m)
          simpa using h
      have h_opt : OPT sigma3 ≤ a1 + a2 + F / (m : ℝ) := by
        have h_le := opt_le_of_schedule (m := m) sigma3 (fun _ : Fin m => a1 + a2 + F / (m : ℝ)) h_sched
        rw [h_mk_uni] at h_le
        exact h_le
      have h_alg_mk : a1 + a2 + F ≤ algorithmMakespan m alg sigma3 := by
        dsimp [algorithmMakespan]
        have h_run : runAlgorithm m alg sigma3 = step (m := m) alg loads2 F := by
          simpa [sigma3, sigma2, sigma1, tau2, runAlgorithm, loads1, loads2, List.foldl_append]
        rw [h_run]
        have h_step : step (m := m) alg loads2 F (alg loads2 F) = loads2 (alg loads2 F) + F := by
          dsimp [step]
          simp
        have h := makespan_ge_each (m := m) (step (m := m) alg loads2 F) (alg loads2 F)
        rw [h_step] at h
        rw [h_loads2 (alg loads2 F)] at h
        nlinarith
      calc
        rho * OPT sigma3 ≤ rho * (a1 + a2 + F / (m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h_opt hrho_nonneg
        _ ≤ a1 + a2 + F := h_final_ratio
        _ ≤ algorithmMakespan m alg sigma3 := h_alg_mk
