/-! ### Paper-order prefix and its OPT bounds -/

/-- The jobs of layers n, n−1, ..., i in the paper's processing order (layer n first). -/
def rudinPrefixJobsR (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) : List ℝ :=
  if i ≤ n then rudinPrefixJobsR eps hOK n (i + 1) ++ rudinLayerJobsC eps hOK n i else []
termination_by n + 1 - i
decreasing_by
  omega

lemma rudinPrefixJobsR_eq (eps : ℝ) (hOK : rudinOK eps) (n : ℕ) (i : ℕ) (hi : i ≤ n) :
    rudinPrefixJobsR eps hOK n i = rudinPrefixJobsR eps hOK n (i + 1) ++ rudinLayerJobsC eps hOK n i := by
  conv =>
    lhs
    unfold rudinPrefixJobsR
  rw [if_pos hi]

/-- The reversed prefix has the same total load as the original one. -/
lemma rudin_totalLoad_R_eq_C (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i ≤ rudinN eps hOK) :
    totalLoad (rudinPrefixJobsR eps hOK (rudinN eps hOK) i) =
      totalLoad (rudinPrefixJobsC eps hOK (rudinN eps hOK) i) := by
  let n := rudinN eps hOK
  have hmain : ∀ d : ℕ, ∀ j : ℕ, n - j = d → j ≤ n →
      totalLoad (rudinPrefixJobsR eps hOK n j) = totalLoad (rudinPrefixJobsC eps hOK n j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro j hdj hle
        by_cases hz : j = n
        · subst j
          rw [rudinPrefixJobsR_eq eps hOK n n (by omega)]
          unfold rudinPrefixJobsR
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp
          rw [rudinPrefixJobsC_eq eps hOK n n le_rfl]
          unfold rudinPrefixJobsC
          rw [if_neg (by omega : ¬ n + 1 ≤ n)]
          simp [totalLoad]
        · have hlt : j < n := lt_of_le_of_ne hle (by intro h; exact hz h.symm)
          have hle' : j + 1 ≤ n := by omega
          have hdiff' : n - (j + 1) < d := by
            rw [← hdj]
            omega
          have hrest := ih (n - (j + 1)) hdiff' (j + 1) rfl hle'
          rw [rudinPrefixJobsR_eq eps hOK n j (le_of_lt hlt)]
          rw [rudinPrefixJobsC_eq eps hOK n j (le_of_lt hlt)]
          rw [show totalLoad (rudinPrefixJobsR eps hOK n (j + 1) ++ rudinLayerJobsC eps hOK n j) =
              totalLoad (rudinPrefixJobsR eps hOK n (j + 1)) + totalLoad (rudinLayerJobsC eps hOK n j) by
                simp [totalLoad]]
          rw [show totalLoad (rudinLayerJobsC eps hOK n j ++ rudinPrefixJobsC eps hOK n (j + 1)) =
              totalLoad (rudinLayerJobsC eps hOK n j) + totalLoad (rudinPrefixJobsC eps hOK n (j + 1)) by
                simp [totalLoad]]
          rw [hrest]
          rw [show j + 1 = j.succ by omega]
          ring
  have h := hmain (n - i) i rfl hi
  dsimp [n] at h
  exact h

/-- OPT of the top two layers in the paper order is at most A + B + 2·A_n^C. -/
lemma rudin_opt_le_top_A4_R (eps : ℝ) (hOK : rudinOK eps) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) (rudinN eps hOK - 1)) ≤
      rudinAC eps hOK (rudinN eps hOK - 1) + rudinBC eps hOK (rudinN eps hOK - 1) +
        2 * rudinAC eps hOK (rudinN eps hOK) := by
  let n := rudinN eps hOK
  have hn : 0 < n := by dsimp [n]; exact rudinN_pos eps hOK
  have hpref : rudinPrefixJobsR eps hOK n (n - 1) =
      rudinPrefixJobsR eps hOK n n ++ rudinLayerJobsC eps hOK n (n - 1) := by
    rw [rudinPrefixJobsR_eq eps hOK n (n - 1) (by omega)]
    have harg : (n - 1) + 1 = n := by
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    rw [harg]
  have hpref2 : rudinPrefixJobsR eps hOK n n = rudinLayerJobsC eps hOK n n := by
    unfold rudinPrefixJobsR
    rw [if_pos le_rfl]
    unfold rudinPrefixJobsR
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp
  let σ := rudinPrefixJobsR eps hOK n (n - 1)
  have h2BC : 2 * rudinBC eps hOK n ≤ rudinAC eps hOK n := by
    dsimp [n]
    exact rudin_two_BC_le_AC eps hOK
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      2 * rudinAC eps hOK n
    else if j = 1 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else if j = 2 then rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) +
      rudinAC eps hOK n + 2 * rudinBC eps hOK n
    else rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ]
    rw [hpref, hpref2]
    have hAC : rudinAC eps hOK (n - 1) = rudinA eps (n - 1) := by
      dsimp [n]
      exact rudinAC_eq_A_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    have hBC : rudinBC eps hOK (n - 1) = rudinB eps (n - 1) := by
      dsimp [n]
      exact rudinBC_eq_B_of_lt eps hOK (rudinN eps hOK - 1) (by omega)
    have hnot : ¬ n < rudinN eps hOK := by dsimp [n]; omega
    have harg : 1 + (n - 1) = n := by
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    have harg2 : (n - 1) + 1 = n := by
      have h1 : 1 ≤ n := by omega
      exact Nat.sub_add_cancel h1
    simp [rudinLayerJobsC, totalLoad, Fin.sum_univ_four, if_neg hnot, harg, harg2]
    ring
  have hmk : makespan 4 loads ≤
      rudinAC eps hOK (n - 1) + rudinBC eps hOK (n - 1) + 2 * rudinAC eps hOK n := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
      nlinarith [h2BC]
    · simp [loads]
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk

/-- OPT of the full prefix of layers n..i (paper order) is at most (3/2)·A_i^C
    for i + 1 ≤ n − 1. -/
lemma rudin_opt_le_full_layer_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i) ≤ 3 / 2 * rudinAC eps hOK i := by
  let n := rudinN eps hOK
  have hile : i ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  have hsum : totalLoad (rudinPrefixJobsR eps hOK n i) = ∑ j : Fin 4, p4 j := by
    have htotR : totalLoad (rudinPrefixJobsR eps hOK n i) =
        totalLoad (rudinPrefixJobsC eps hOK n i) := by
      dsimp [n]
      exact rudin_totalLoad_R_eq_C eps hOK i (by dsimp [n]; omega)
    rw [htotR]
    dsimp [n]
    simpa [totalLoad] using h4sum
  have hmk : makespan 4 p4 ≤ 3 / 2 * rudinAC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    exact h4le j
  exact le_trans (opt_le_of_schedule (m := 4) (rudinPrefixJobsR eps hOK n i) p4 hsum) hmk

/-- OPT of the B-row prefix (paper order, layers n..i+1 plus the whole B-row of i)
    is at most B_i + (3/2)·A_{i+1} for i + 1 ≤ n − 1. -/
lemma rudin_opt_le_full_B_row_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ)
    (hi : i.succ < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
      List.replicate 4 (rudinBC eps hOK i)) ≤
      rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
  let n := rudinN eps hOK
  have hile : i + 1 ≤ n := by dsimp [n]; omega
  have hpack := rudin_packing_C eps hOK i.succ hile
  rcases hpack.1 with ⟨p4, h4le, h4sum⟩
  have hB : 0 ≤ rudinBC eps hOK i := by
    dsimp [n]
    exact rudinBC_nonneg eps hOK i (by omega)
  let loads : Loads 4 := fun j => rudinBC eps hOK i + p4 j
  have hsum : totalLoad (rudinPrefixJobsR eps hOK n i.succ ++
      List.replicate 4 (rudinBC eps hOK i)) = ∑ j : Fin 4, loads j := by
    dsimp [loads]
    have htotR : totalLoad (rudinPrefixJobsR eps hOK n i.succ) =
        totalLoad (rudinPrefixJobsC eps hOK n i.succ) := by
      dsimp [n]
      exact rudin_totalLoad_R_eq_C eps hOK i.succ (by dsimp [n]; omega)
    rw [htotR]
    have h4sum' : (rudinPrefixJobsC eps hOK n (i + 1)).sum = ∑ j : Fin 4, p4 j := by
      have hsucc : i.succ = i + 1 := by omega
      dsimp [n]
      simpa [hsucc, totalLoad] using h4sum
    simp [totalLoad]
    rw [h4sum']
    simp [Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinBC eps hOK i + 3 / 2 * rudinAC eps hOK i.succ := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    simp [loads]
    nlinarith [h4le j, hB]
  exact le_trans (opt_le_of_schedule (m := 4)
    (rudinPrefixJobsR eps hOK n i.succ ++ List.replicate 4 (rudinBC eps hOK i)) loads hsum) hmk

/-- OPT of the three-A prefix (paper order) is at most A_i + B_i. -/
lemma rudin_opt_le_A3_R (eps : ℝ) (hOK : rudinOK eps) (i : ℕ) (hi : i < rudinN eps hOK) :
    OPT (rudinPrefixJobsR eps hOK (rudinN eps hOK) i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
  let n := rudinN eps hOK
  have hle' : i.succ ≤ rudinN eps hOK := by dsimp [n]; omega
  have htotR : totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤
      totalLoad (rudinPrefixJobsC eps hOK n i.succ) := by
    dsimp [n]
    rw [rudin_totalLoad_R_eq_C eps hOK i.succ (by dsimp [n]; omega)]
  have htot := rudin_totalLoad_C_le eps hOK i.succ hle'
  have hq : rudinA eps i.succ ≤ 1 / 4 * rudinA eps i :=
    rudinA_succ_le_quarter eps hOK i hle'
  have hS' : rudinS eps i.succ = rudinM eps * rudinA eps i := rudinS_succ eps i
  have hAC : rudinAC eps hOK i = rudinA eps i := rudinAC_eq_A_of_lt eps hOK i hi
  have hBC : rudinBC eps hOK i = rudinB eps i := rudinBC_eq_B_of_lt eps hOK i hi
  have hB : 0 ≤ rudinBC eps hOK i := by
    dsimp [n]
    exact rudinBC_nonneg eps hOK i (by omega)
  have hApos : 0 < rudinA eps i := by
    rcases rudin_pos_le_n eps hOK i (le_of_lt hi) with ⟨hS, hA, hR, hR0⟩
    exact hA
  have hload4 : rudinBC eps hOK i + totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤
      rudinAC eps hOK i + rudinBC eps hOK i := by
    by_cases hz : i.succ < rudinN eps hOK
    · have hq2 : rudinA eps i.succ.succ ≤ 1 / 4 * rudinA eps i.succ :=
        rudinA_succ_le_quarter eps hOK i.succ (by omega)
      have htot' : totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤
          4 * rudinS eps i.succ + 8 / 3 * rudinA eps i.succ.succ := by
        rw [htotR]
        rw [hS'] at htot
        simp [hz] at htot
        exact htot
      rw [hAC, hBC]
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot', hq, hq2, hlt, hApos]
    · have hz'' : i.succ = rudinN eps hOK := le_antisymm hle' (le_of_not_gt hz)
      have htot' : totalLoad (rudinPrefixJobsR eps hOK n i.succ) ≤ 4 * rudinS eps i.succ := by
        rw [htotR]
        rw [hS', hz''] at htot
        simp [hz''] at htot
        exact htot
      rw [hAC, hBC]
      dsimp [n]
      have hlt : rudinM eps < 1 / 10 := rudinM_lt_one_tenth eps hOK
      nlinarith [htot', hlt, hApos]
  let σ := rudinPrefixJobsR eps hOK n i.succ ++
      [rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i, rudinBC eps hOK i,
       rudinAC eps hOK i, rudinAC eps hOK i, rudinAC eps hOK i]
  let loads : Loads 4 := fun j =>
    if j = 0 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 1 then rudinAC eps hOK i + rudinBC eps hOK i
    else if j = 2 then rudinAC eps hOK i + rudinBC eps hOK i
    else rudinBC eps hOK i + totalLoad (rudinPrefixJobsR eps hOK n i.succ)
  have hsum : totalLoad σ = ∑ j : Fin 4, loads j := by
    dsimp [σ, loads]
    simp [totalLoad, Fin.sum_univ_four]
    ring
  have hmk : makespan 4 loads ≤ rudinAC eps hOK i + rudinBC eps hOK i := by
    dsimp [makespan]
    apply Finset.sup'_le
    intro j hj
    fin_cases j
    · simp [loads]
    · simp [loads]
    · simp [loads]
    · simp [loads]
      exact hload4
  exact le_trans (opt_le_of_schedule (m := 4) σ loads hsum) hmk
