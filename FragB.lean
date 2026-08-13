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
    congr 1
    omega
  have hB : 0 ≤ rudinBC eps hOK i := by
    dsimp [n]
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
      · dsimp [σB]
        exact rudin_top_B_violation_ratio_R eps hOK hmk
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
        exact le_trans hload (makespan_ge_each (m := 4)
          (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
            List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j)
      have hRatio : (1 + rudinV eps) * OPT σA3 ≤ makespan 4 (runAlgorithm 4 alg σA3) := by
        dsimp [σA3]
        have hopt : OPT (rudinPrefixJobsR eps hOK n i.succ ++
            [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
             rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
            rudinAC eps hOK i + rudinBC eps hOK i := rudin_opt_le_A3_R eps hOK i hi
        have hratio := rudin_A23_ratio_ge_C eps hOK i hi
        have hden : 0 < rudinAC eps hOK i + rudinBC eps hOK i := by
          have hA' : 0 < rudinA eps i := by
            rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
            exact hA
          have hB' : 0 < rudinB eps i := rudinB_pos_lt_n eps hOK i hi
          rw [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi]
          nlinarith
        have hprod : (1 + rudinV eps) * (rudinAC eps hOK i + rudinBC eps hOK i) ≤
            rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i := by
          have h := (le_div_iff₀ hden).mp hratio
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
      let σA4 := rudinPrefixJobsR eps hOK n i.succ ++
        [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
         rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i, big]
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
          dsimp [σA4, big, j0]
          have hload : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i + big ≤
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
                 rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i, big])) j0 := by
            rw [hstep]
            dsimp [step]
            simp
          have hbase : rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
              2 * rudinAC eps hOK i.succ ≤
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j0 + rudinAC eps hOK i + big := by
            dsimp [big]
            nlinarith [hinv j0, hBsplit2 j0, hcoll]
          exact le_trans hbase (le_trans hload (makespan_ge_each (m := 4)
            (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
               rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i, big])) j0))
        have hRatio : (1 + rudinV eps) * OPT σA4 ≤ makespan 4 (runAlgorithm 4 alg σA4) := by
          dsimp [σA4, big]
          have hVpos : 0 < 1 + rudinV eps := by nlinarith [rudinV_pos eps hOK]
          by_cases htop : i.succ = rudinN eps hOK
          · have hopt : OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
                  2 * rudinAC eps hOK (rudinN eps hOK) := rudin_opt_le_top_A4_R eps hOK
            have hratio := rudin_top_A4_ratio_ge eps hOK
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
              have h := (le_div_iff₀ hden).mp hratio
              nlinarith
            have h1 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                rudinS eps (rudinN eps hOK) + rudinBC eps hOK (rudinN eps hOK - 1) +
                  2 * rudinAC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK) := by
              have h2 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                  (1 + rudinV eps) * (rudinAC eps hOK (rudinN eps hOK - 1) +
                    rudinBC eps hOK (rudinN eps hOK - 1) + 2 * rudinAC eps hOK (rudinN eps hOK)) := by
                exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
              exact le_trans h2 hprod
            have hfinal : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1)) ≤
                makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n (rudinN eps hOK - 1))) := by
              exact le_trans h1 (by
                dsimp [n] at hmk
                dsimp [n]
                simpa [htop] using hmk)
            dsimp [n] at hfinal
            exact hfinal
          · have hopt : OPT (rudinPrefixJobsR eps hOK n i) ≤ 3 / 2 * rudinAC eps hOK i :=
              rudin_opt_le_full_layer_R eps hOK i (by omega)
            have hratio := rudin_A4_ratio_ge_C eps hOK i (by omega)
            have hden : 0 < 3 / 2 * rudinAC eps hOK i := by
              have hA' : 0 < rudinA eps i := by
                rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
                exact hA
              rw [rudinAC_eq_A_of_lt eps hOK i hi]
              positivity
            have hprod : (1 + rudinV eps) * (3 / 2 * rudinAC eps hOK i) ≤
                rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                  2 * rudinAC eps hOK i.succ := by
              have h := (le_div_iff₀ hden).mp hratio
              nlinarith
            have h1 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i) ≤
                rudinS eps i.succ + rudinBC eps hOK i + 2 * rudinAC eps hOK i +
                  2 * rudinAC eps hOK i.succ := by
              have h2 : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i) ≤
                  (1 + rudinV eps) * (3 / 2 * rudinAC eps hOK i) := by
                exact mul_le_mul_of_nonneg_left hopt (le_of_lt hVpos)
              exact le_trans h2 hprod
            have hfinal : (1 + rudinV eps) * OPT (rudinPrefixJobsR eps hOK n i) ≤
                makespan 4 (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i)) := by
              exact le_trans h1 (by
                dsimp [n] at hmk
                dsimp [n]
                simpa [σA4, big] using hmk)
            dsimp [n] at hfinal
            exact hfinal
        refine ⟨σA4, ?_, hRatio⟩
        rw [hpref]
        exact ⟨[], by
          change rudinPrefixJobsR eps hOK n i ++ [] = rudinPrefixJobsR eps hOK n i
          simp⟩
      · right
        intro j
        by_cases hj : j = j0
        · subst j
          have hload : (runAlgorithm 4 alg σA4) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 + big := by
            dsimp [σA4, j0]
            rw [hstep]
            dsimp [step]
            simp
          have hfresh : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j0 := by
            rcases hAcase j0 with hA | hB
            · exfalso
              exact hcoll hA
            · exact hB
          have hA' : 0 ≤ rudinAC eps hOK i.succ := by
            rcases rudin_pos_le_n eps hOK i.succ (by omega) with ⟨hS, hA, hR, hR0⟩
            exact le_of_lt hA
          have hSi : rudinS eps i = rudinS eps i.succ + rudinBC eps hOK i + rudinAC eps hOK i := by
            have hS' : rudinS eps i = rudinA eps i + rudinB eps i + rudinS eps i.succ :=
              rudinS_eq_add_of_lt eps hOK i hi
            rw [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi] at hS'
            rw [hS']
            ring
          rw [hload, hfresh]
          dsimp [big]
          rw [hSi]
          nlinarith [hinv j0, hBsplit2 j0, hA']
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
              nlinarith [hge, hApos]
            rcases hAcase jj with hA | hB
            · nlinarith [hA, hbig]
            · nlinarith [hB, hbig]
          have hk_j0 : k j0 = 0 := by
            have h1 := hk j0
            have h2 : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j0 =
                (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                  List.replicate 4 (rudinBC eps hOK i))) j0 := by
              rcases hAcase j0 with hA | hB
              · exfalso
                exact hcoll hA
              · exact hB
            have hApos : 0 < rudinAC eps hOK i := by
              rw [rudinAC_eq_A_of_lt eps hOK i hi]
              rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
              exact hA
            have hk0R : (k j0 : ℝ) = 0 := by
              nlinarith [h1, h2, hApos]
            exact_mod_cast hk0R
          have hk_j : k j = 1 := by
            by_contra h
            have hk0 : k j = 0 := by omega
            have hle0 : k 0 ≤ 1 := hk_le 0
            have hle1 : k 1 ≤ 1 := hk_le 1
            have hle2 : k 2 ≤ 1 := hk_le 2
            have hle3 : k 3 ≤ 1 := hk_le 3
            fin_cases j <;> fin_cases j0 <;> simp at hj ⊢ <;>
              simp [hk0, hk_j0, hle0, hle1, hle2, hle3, Fin.sum_univ_four] at hk_sum ⊢ <;> omega
          have hloadsA : (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
              List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i))) j + rudinAC eps hOK i := by
            rw [hk j, hk_j]
            ring
          have hload' : (runAlgorithm 4 alg σA4) j =
              (runAlgorithm 4 alg (rudinPrefixJobsR eps hOK n i.succ ++
                List.replicate 4 (rudinBC eps hOK i) ++ List.replicate 3 (rudinAC eps hOK i))) j := by
            dsimp [σA4, j0]
            rw [hstep]
            dsimp [step]
            simp [hj]
          have hSi : rudinS eps i = rudinS eps i.succ + rudinBC eps hOK i + rudinAC eps hOK i := by
            have hS' : rudinS eps i = rudinA eps i + rudinB eps i + rudinS eps i.succ :=
              rudinS_eq_add_of_lt eps hOK i hi
            rw [rudinAC_eq_A_of_lt eps hOK i hi, rudinBC_eq_B_of_lt eps hOK i hi] at hS'
            rw [hS']
            ring
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
    · right
      exact rudin_layer_step_R eps hOK alg i hi hsplit
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
  have hpack := rudin_packing_C eps hOK 0 (by dsimp [n]; omega)
  rcases hpack.2 with ⟨p3, h3le, h3sum⟩
  have htotR : totalLoad (rudinPrefixJobsR eps hOK n 0) =
      totalLoad (rudinPrefixJobsC eps hOK n 0) := by
    dsimp [n]
    exact rudin_totalLoad_R_eq_C eps hOK 0 (by dsimp [n]; omega)
  let σ := rudinPrefixJobsR eps hOK n 0 ++ [2 * rudinAC eps hOK 0]
  let loads : Loads 4 := fun j => if h : j.val < 3 then p3 ⟨j.val, h⟩ else 2 * rudinAC eps hOK 0
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    rw [htotR]
    have h3sum' : (rudinPrefixJobsC eps hOK n 0).sum = ∑ j : Fin 3, p3 j := by
      dsimp [n]
      simpa [totalLoad] using h3sum
    simp [totalLoad, Fin.sum_univ_four, Fin.sum_univ_three]
    rw [h3sum']
    ring
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
    dsimp [j0]
    have hload : (runAlgorithm 4 alg σ) j0 + 2 * rudinAC eps hOK 0 ≤
        (runAlgorithm 4 alg (σ ++ [2 * rudinAC eps hOK 0])) j0 := by
      rw [hstep]
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
  dsimp [σ]
  exact le_trans h1 hmk0

/-- The adversary: for every ε > 0 the construction forces a ratio ≥ √3 − ε. -/
theorem rudin_m4_adversary_exists (epsilon : ℝ) (heps_pos : 0 < epsilon)
    (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence,
      algorithmMakespan 4 alg sigma ≥ (Real.sqrt 3 - epsilon) * OPT sigma := by
  let eps' := min epsilon (1 / 100 : ℝ)
  have hOK : rudinOK eps' := by
    dsimp [eps', rudinOK]
    constructor
    · exact lt_min heps_pos (by norm_num)
    · exact lt_of_le_of_lt (min_le_right epsilon (1 / 100 : ℝ)) (by norm_num)
  rcases rudin_layer_separation eps' hOK alg with hviol | hsplit
  · rcases hviol with ⟨σ', hpref', hv⟩
    refine ⟨σ', ?_⟩
    have hV : 1 + rudinV eps' = Real.sqrt 3 - eps' := by dsimp [rudinV]; ring
    have hle : Real.sqrt 3 - epsilon ≤ Real.sqrt 3 - eps' := by
      have hmin : eps' ≤ epsilon := min_le_left epsilon (1 / 100 : ℝ)
      nlinarith
    nlinarith [hv, hV, hle]
  · refine ⟨rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
      [2 * rudinAC eps' hOK 0], ?_⟩
    have hf := rudin_final_job_forces eps' hOK alg hsplit
    have hV : 1 + rudinV eps' = Real.sqrt 3 - eps' := by dsimp [rudinV]; ring
    have hle : Real.sqrt 3 - epsilon ≤ Real.sqrt 3 - eps' := by
      have hmin : eps' ≤ epsilon := min_le_left epsilon (1 / 100 : ℝ)
      nlinarith
    have hOPTpos : 0 ≤ OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
        [2 * rudinAC eps' hOK 0]) := by
      have h1 : maxJobSize (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
          [2 * rudinAC eps' hOK 0]) ≤
          OPT (rudinPrefixJobsR eps' hOK (rudinN eps' hOK) 0 ++
            [2 * rudinAC eps' hOK 0]) := opt_ge_max_job _
      exact le_trans (maxJobSize_nonneg _) h1
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
