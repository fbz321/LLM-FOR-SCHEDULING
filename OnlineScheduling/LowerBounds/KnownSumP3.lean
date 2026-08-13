/-
P2||Cmax with Known Total Sum: Lower Bound 4/3 (Kellerer et al., 1997)

Adaptive adversary (m=2):
1. Send [1/3, 1/3].
2. If same machine → [2/3, 2/3] (case 1). By pigeonhole on 2 machines,
   some machine ends with ≥ 4/3. OPT = 1, ratio = 4/3.
3. If different → [1, 1/3] (case 2). makespan ≥ 4/3, OPT = 1, ratio = 4/3.
-/

import OnlineScheduling.Basic

open Finset

namespace OnlineScheduling

noncomputable def ks2_case1 : JobSequence := [1 / 3, 1 / 3, 2 / 3, 2 / 3]
noncomputable def ks2_case2 : JobSequence := [1 / 3, 1 / 3, 1, 1 / 3]

theorem ks2_known_sum_lower_bound (alg : OnlineAlgorithm 2) :
    (algorithmMakespan 2 alg ks2_case1 ≥ (4 / 3 : ℝ) * OPT ks2_case1)
    ∨ (algorithmMakespan 2 alg ks2_case2 ≥ (4 / 3 : ℝ) * OPT ks2_case2) := by
  -- First two 1/3 jobs
  let m1 := alg (λ _ => 0) (1/3 : ℝ)
  let loads1 : Loads 2 := runAlgorithm 2 alg [1/3]
  let m2 := alg loads1 (1/3 : ℝ)
  let loads2 : Loads 2 := runAlgorithm 2 alg [1/3, 1/3]

  have h_loads1_m1 : loads1 m1 = (1/3 : ℝ) := by
    unfold loads1 runAlgorithm
    simp [step, m1]

  -- OPT of both cases = 1
  have h_opt1 : OPT ks2_case1 = (1 : ℝ) := by
    apply opt_eq_of_const_schedule (m := 2) ks2_case1 (1 : ℝ)
    norm_num [ks2_case1, totalLoad]
  have h_opt2 : OPT ks2_case2 = (1 : ℝ) := by
    apply opt_eq_of_const_schedule (m := 2) ks2_case2 (1 : ℝ)
    norm_num [ks2_case2, totalLoad]

  by_cases h_same : m1 = m2
  · -- Case 1: both 1/3's on m1 → m1 has 2/3
    left; rw [h_opt1]
    have hm2_eq_m1 : m2 = m1 := h_same.symm
    -- After [1/3, 1/3]: loads2 m1 = 2/3, loads2 j = 0 for j ≠ m1
    have h_loads2_m1 : loads2 m1 = (2/3 : ℝ) := by
      have h_run : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
        simp [loads2, runAlgorithm, loads1]
      have hm2_def : alg loads1 (1/3 : ℝ) = m1 := by exact hm2_eq_m1
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1_m1]
        norm_num
      · exfalso
        exact hif hm2_def.symm
    have h_loads2_other (j : Fin 2) (hj : j ≠ m1) : loads2 j = (0 : ℝ) := by
      have h_run : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
        simp [loads2, runAlgorithm, loads1]
      have hm2_def : alg loads1 (1/3 : ℝ) = m1 := by exact hm2_eq_m1
      have h_loads1_other : loads1 j = (0 : ℝ) := by
        change (step (m := 2) alg (λ _ => 0) (1/3 : ℝ)) j = 0
        dsimp [step]
        split_ifs with hif
        · exfalso
          exact hj (by simpa [m1] using hif)
        · simp
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · exfalso
        exact hj (by simpa [← hm2_def] using hif)
      · simp [h_loads1_other]

    -- Now [2/3, 2/3]. Let m3, m4 be target machines.
    let m3 := alg loads2 (2/3 : ℝ)
    let loads3 : Loads 2 := step (m := 2) alg loads2 (2/3 : ℝ)
    let m4 := alg loads3 (2/3 : ℝ)
    let loads4 : Loads 2 := step (m := 2) alg loads3 (2/3 : ℝ)
    have h_run4 : runAlgorithm 2 alg ks2_case1 = loads4 := by
      simp [ks2_case1, runAlgorithm, loads4, loads3, loads2, loads1]

    -- {m1, m3} covers Fin 2 if m3 ≠ m1
    have h_covers13 (h_ne : m3 ≠ m1) : ({m1, m3} : Finset (Fin 2)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.subset_univ _
      · rw [Finset.card_univ, Fintype.card_fin]
        have hcard : ({m1, m3} : Finset (Fin 2)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using h_ne.symm)]
          simp
        rw [hcard]

    -- Prove makespan ≥ 4/3 by case analysis
    have h_makespan_ge : (4/3 : ℝ) ≤ makespan 2 loads4 := by
      by_cases h_m3_eq_m1 : m3 = m1
      · -- First 2/3 on m1 → loads3 m1 = 4/3; monotonic → loads4 m1 ≥ 4/3
        have h_loads3_m1 : loads3 m1 = (4/3 : ℝ) := by
          have hm3_def : alg loads2 (2/3 : ℝ) = m1 := by simpa [m3] using h_m3_eq_m1
          dsimp [loads3, step]
          split_ifs with hif
          · simp [h_loads2_m1]
            norm_num
          · exfalso
            exact hif hm3_def.symm
        have h_le : loads3 m1 ≤ loads4 m1 := by
          dsimp [loads4, step]; split_ifs <;> nlinarith [h_loads3_m1]
        have h := makespan_ge_each (m := 2) loads4 m1
        nlinarith
      · -- m3 ≠ m1 → loads3 m3 = 2/3 (was 0, got +2/3), loads3 m1 = 2/3 (unchanged)
        have h_loads3_m3 : loads3 m3 = (2/3 : ℝ) := by
          have hm3_def : alg loads2 (2/3 : ℝ) = m3 := by rfl
          dsimp [loads3, step]
          split_ifs with hif
          · simp [h_loads2_other m3 h_m3_eq_m1]
          · exfalso
            exact hif hm3_def.symm
        have h_loads3_m1 : loads3 m1 = (2/3 : ℝ) := by
          have hm3_def : alg loads2 (2/3 : ℝ) = m3 := by rfl
          dsimp [loads3, step]
          split_ifs with hif
          · exfalso
            exact h_m3_eq_m1 (by simpa [hm3_def] using hif.symm)
          · simp [h_loads2_m1]
        -- m4 must be m1 or m3
        have h_m4_cases : m4 = m1 ∨ m4 = m3 := by
          have h_mem : m4 ∈ ({m1, m3} : Finset (Fin 2)) := by
            rw [h_covers13 h_m3_eq_m1]; exact Finset.mem_univ _
          simp at h_mem; exact h_mem
        rcases h_m4_cases with (h_m4_eq_m1 | h_m4_eq_m3)
        · have h_loads4_m1 : loads4 m1 = (4/3 : ℝ) := by
            have hm4_def : alg loads3 (2/3 : ℝ) = m1 := by simpa [m4] using h_m4_eq_m1
            dsimp [loads4, step]
            split_ifs with hif
            · simp [h_loads3_m1]
              norm_num
            · exfalso
              exact hif hm4_def.symm
          have h := makespan_ge_each (m := 2) loads4 m1
          rw [h_loads4_m1] at h; exact h
        · have h_loads4_m3 : loads4 m3 = (4/3 : ℝ) := by
            have hm4_def : alg loads3 (2/3 : ℝ) = m3 := by simpa [m4] using h_m4_eq_m3
            dsimp [loads4, step]
            split_ifs with hif
            · simp [h_loads3_m3]
              norm_num
            · exfalso
              exact hif hm4_def.symm
          have h := makespan_ge_each (m := 2) loads4 m3
          rw [h_loads4_m3] at h; exact h

    dsimp [algorithmMakespan]; rw [h_run4]; simpa using h_makespan_ge

  · -- Case 2: different machines → each has 1/3
    right; rw [h_opt2]
    -- After [1/3, 1/3]: each machine has 1/3 (since m1 ≠ m2 on Fin 2)
    have h_m1_cases : m1 = (0 : Fin 2) ∨ m1 = (1 : Fin 2) := by
      have h_mem : m1 ∈ ({0,1} : Finset (Fin 2)) := Finset.mem_univ _
      simpa using h_mem
    have h_m2_cases : m2 = (0 : Fin 2) ∨ m2 = (1 : Fin 2) := by
      have h_mem : m2 ∈ ({0,1} : Finset (Fin 2)) := Finset.mem_univ _
      simpa using h_mem
    have h_m1_m2_cases : (m1 = (0 : Fin 2) ∧ m2 = (1 : Fin 2))
                       ∨ (m1 = (1 : Fin 2) ∧ m2 = (0 : Fin 2)) := by
      rcases h_m1_cases with (hm1 | hm1) <;> rcases h_m2_cases with (hm2 | hm2)
      · exfalso; exact h_same (hm1.trans hm2.symm)
      · left; exact ⟨hm1, hm2⟩
      · right; exact ⟨hm1, hm2⟩
      · exfalso; exact h_same (hm1.trans hm2.symm)
    have h_each_one_third : ∀ i : Fin 2, loads2 i = (1/3 : ℝ) := by
      intro i
      rcases h_m1_m2_cases with ((⟨hm1, hm2⟩) | (⟨hm1, hm2⟩))
      · have hm1' : alg (λ _ : Fin 2 => 0) (1/3 : ℝ) = (0 : Fin 2) := by
          simpa [m1] using hm1
        have hm2' : alg loads1 (1/3 : ℝ) = (1 : Fin 2) := by
          simpa [m2] using hm2
        have h0 : loads2 (0 : Fin 2) = (1/3 : ℝ) := by
          have h_run2 : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
            simp [loads2, runAlgorithm, loads1]
          have h_loads1_0 : loads1 (0 : Fin 2) = (1/3 : ℝ) := by
            change (step (m := 2) alg (λ _ => 0) (1/3 : ℝ)) (0 : Fin 2) = 1/3
            dsimp [step]
            split_ifs with hif
            · simp
            · exfalso
              exact hif hm1'.symm
          have h_not : (0 : Fin 2) ≠ alg loads1 (1/3 : ℝ) := by
            intro h
            rw [hm2'] at h
            exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) h
          rw [h_run2]; dsimp [step]
          split_ifs with hif
          · exfalso
            rw [hm2'] at hif
            exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hif
          · simp [h_loads1_0]
        have h1 : loads2 (1 : Fin 2) = (1/3 : ℝ) := by
          have h_run2 : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
            simp [loads2, runAlgorithm, loads1]
          have h_loads1_1 : loads1 (1 : Fin 2) = (0 : ℝ) := by
            change (step (m := 2) alg (λ _ => 0) (1/3 : ℝ)) (1 : Fin 2) = 0
            dsimp [step]
            split_ifs with hif
            · exfalso
              rw [hm1'] at hif
              exact (by decide : (1 : Fin 2) ≠ (0 : Fin 2)) hif
            · simp
          rw [h_run2]; dsimp [step]
          split_ifs with hif
          · simp [h_loads1_1]
          · exfalso
            exact hif hm2'.symm
        fin_cases i <;> simpa [h0, h1]
      · have hm1' : alg (λ _ : Fin 2 => 0) (1/3 : ℝ) = (1 : Fin 2) := by
          simpa [m1] using hm1
        have hm2' : alg loads1 (1/3 : ℝ) = (0 : Fin 2) := by
          simpa [m2] using hm2
        have h0 : loads2 (0 : Fin 2) = (1/3 : ℝ) := by
          have h_run2 : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
            simp [loads2, runAlgorithm, loads1]
          have h_loads1_0 : loads1 (0 : Fin 2) = (0 : ℝ) := by
            change (step (m := 2) alg (λ _ => 0) (1/3 : ℝ)) (0 : Fin 2) = 0
            dsimp [step]
            split_ifs with hif
            · exfalso
              rw [hm1'] at hif
              exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) hif
            · simp
          rw [h_run2]; dsimp [step]
          split_ifs with hif
          · simp [h_loads1_0]
          · exfalso
            exact hif hm2'.symm
        have h1 : loads2 (1 : Fin 2) = (1/3 : ℝ) := by
          have h_run2 : loads2 = step (m := 2) alg loads1 (1/3 : ℝ) := by
            simp [loads2, runAlgorithm, loads1]
          have h_loads1_1 : loads1 (1 : Fin 2) = (1/3 : ℝ) := by
            change (step (m := 2) alg (λ _ => 0) (1/3 : ℝ)) (1 : Fin 2) = 1/3
            dsimp [step]
            split_ifs with hif
            · simp
            · exfalso
              exact hif hm1'.symm
          have h_not : (1 : Fin 2) ≠ alg loads1 (1/3 : ℝ) := by
            intro h
            rw [hm2'] at h
            exact (by decide : (1 : Fin 2) ≠ (0 : Fin 2)) h
          rw [h_run2]; dsimp [step]
          split_ifs with hif
          · exfalso
            rw [hm2'] at hif
            exact (by decide : (1 : Fin 2) ≠ (0 : Fin 2)) hif
          · simp [h_loads1_1]
        fin_cases i <;> simpa [h0, h1]
    -- Add [1]: whichever machine gets it, load = 1/3+1 = 4/3
    let m3 := alg loads2 (1 : ℝ)
    let loads3 : Loads 2 := step (m := 2) alg loads2 (1 : ℝ)
    have h_loads3_m3 : loads3 m3 = (4/3 : ℝ) := by
      dsimp [loads3, step]
      split_ifs with hif
      · simp [h_each_one_third m3]
        norm_num
      · exfalso
        exact hif rfl
    -- Add [1/3]: doesn't reduce m3's load
    let m4 := alg loads3 (1/3 : ℝ)
    let loads4 : Loads 2 := step (m := 2) alg loads3 (1/3 : ℝ)
    have h_run4 : runAlgorithm 2 alg ks2_case2 = loads4 := by
      simp [ks2_case2, runAlgorithm, loads4, loads3, loads2, loads1]
    have h_loads4_m3_ge : (4/3 : ℝ) ≤ loads4 m3 := by
      have h_le : loads3 m3 ≤ loads4 m3 := by
        dsimp [loads4, step, m4]; split <;> simp
      rw [h_loads3_m3] at h_le; exact h_le
    dsimp [algorithmMakespan]; rw [h_run4]
    have h := makespan_ge_each (m := 2) loads4 m3
    nlinarith

end OnlineScheduling
