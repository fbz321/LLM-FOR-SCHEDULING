/-
Decreasing Job Sizes Semi-Online Lower Bounds (Seiden, Sgall, Woeginger 2000)

m=2: lower bound 7/6 (tight, LPT achieves it)
m=3: lower bound (1+√37)/6 ≈ 1.18046
-/

import OnlineScheduling.Basic

open Finset

namespace OnlineScheduling

/-! ### m=2: Lower Bound 7/6

  Adaptive adversary:
  1. Send [3, 3].
     - Same machine → makespan ≥ 6, OPT = 3, ratio = 2 > 7/6.
     - Different machines → send [2, 2, 2].
       Pigeonhole: 3×2 on 2 machines → some machine gets ≥ 2 of the 2's.
       Load ≥ 3+4 = 7. OPT = 6. Ratio = 7/6.
-/

theorem dec2_lower_bound (alg : OnlineAlgorithm 2) :
    ∃ (sigma : JobSequence), algorithmMakespan 2 alg sigma ≥ (7/6 : ℝ) * OPT sigma := by
  let m1 : Fin 2 := alg (λ _ => 0) (3 : ℝ)
  let loads1 : Loads 2 := runAlgorithm 2 alg [3]
  let m2 : Fin 2 := alg loads1 (3 : ℝ)
  let loads2 : Loads 2 := runAlgorithm 2 alg [3, 3]

  have h_loads1_m1 : loads1 m1 = (3 : ℝ) := by
    change (step (m := 2) alg (λ _ => 0) (3 : ℝ)) m1 = 3
    dsimp [step]
    split_ifs with hif
    · simp
    · exfalso
      exact hif rfl

  have h_opt_three : OPT [3, 3] = (3 : ℝ) := by
    apply opt_eq_of_const_schedule (m := 2) [3, 3] (3 : ℝ)
    norm_num [totalLoad]

  by_cases h_same : m1 = m2
  · -- Same machine: stop at [3, 3].
    use [3, 3]
    have h_run2 : runAlgorithm 2 alg [3, 3] = loads2 := by
      simp [runAlgorithm, loads1, loads2]
    have hm2_def : alg loads1 (3 : ℝ) = m1 := by exact h_same.symm
    have h_loads2_m1 : loads2 m1 = (6 : ℝ) := by
      have h_run : loads2 = step (m := 2) alg loads1 (3 : ℝ) := by
        simp [loads2, runAlgorithm, loads1]
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1_m1]
        ring
      · exfalso
        exact hif hm2_def.symm
    have h_mk : (6 : ℝ) ≤ algorithmMakespan 2 alg [3, 3] := by
      dsimp [algorithmMakespan]
      rw [h_run2]
      have h := makespan_ge_each (m := 2) loads2 m1
      rw [h_loads2_m1] at h
      exact h
    calc
      (7 / 6 : ℝ) * OPT [3, 3] ≤ (7 / 6 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h_opt_three.le (by norm_num)
      _ ≤ 6 := by norm_num
      _ ≤ algorithmMakespan 2 alg [3, 3] := h_mk

  · -- Different machines: each has 3, then [2, 2, 2] forces makespan ≥ 7.
    use [3, 3, 2, 2, 2]
    have h_run2 : loads2 = step (m := 2) alg loads1 (3 : ℝ) := by
      simp [loads2, runAlgorithm, loads1]
    have hm1_def : alg (λ _ : Fin 2 => 0) (3 : ℝ) = m1 := by rfl
    have hm2_def : alg loads1 (3 : ℝ) = m2 := by rfl
    have h_loads1_m2 : loads1 m2 = (0 : ℝ) := by
      change (step (m := 2) alg (λ _ => 0) (3 : ℝ)) m2 = 0
      dsimp [step]
      split_ifs with hif
      · exfalso
        exact h_same (by simpa [m1] using hif.symm)
      · simp
    have h_loads2_m1 : loads2 m1 = (3 : ℝ) := by
      rw [h_run2]; dsimp [step]
      split_ifs with hif
      · exfalso
        exact h_same (by simpa [hm2_def] using hif)
      · simp [h_loads1_m1]
    have h_loads2_m2 : loads2 m2 = (3 : ℝ) := by
      rw [h_run2]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1_m2]
      · exfalso
        exact hif rfl
    have h_covers : ({m1, m2} : Finset (Fin 2)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.subset_univ _
      · rw [Finset.card_univ, Fintype.card_fin]
        have hcard : ({m1, m2} : Finset (Fin 2)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using h_same)]
          simp
        rw [hcard]
    have h_all_three : ∀ i : Fin 2, loads2 i = (3 : ℝ) := by
      intro i
      have hi : i ∈ ({m1, m2} : Finset (Fin 2)) := by
        rw [h_covers]; exact Finset.mem_univ i
      simp at hi
      rcases hi with hi1 | hi2
      · rw [hi1]
        exact h_loads2_m1
      · rw [hi2]
        exact h_loads2_m2
    -- Three jobs of size 2
    let m3 : Fin 2 := alg loads2 (2 : ℝ)
    let loads3 : Loads 2 := step (m := 2) alg loads2 (2 : ℝ)
    let m4 : Fin 2 := alg loads3 (2 : ℝ)
    let loads4 : Loads 2 := step (m := 2) alg loads3 (2 : ℝ)
    let m5 : Fin 2 := alg loads4 (2 : ℝ)
    let loads5 : Loads 2 := step (m := 2) alg loads4 (2 : ℝ)
    have h_runFinal : runAlgorithm 2 alg [3, 3, 2, 2, 2] = loads5 := by
      simp [runAlgorithm, loads1, loads2, loads3, loads4, loads5]
    have h_dup : m3 = m4 ∨ m3 = m5 ∨ m4 = m5 := by
      by_contra hnd
      push_neg at hnd
      have hc : ({m3, m4} : Finset (Fin 2)) = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.subset_univ _
        · rw [Finset.card_univ, Fintype.card_fin]
          have hcard : ({m3, m4} : Finset (Fin 2)).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simpa using hnd.1)]
            simp
          rw [hcard]
      have hm5 : m5 ∈ ({m3, m4} : Finset (Fin 2)) := by
        rw [hc]; exact Finset.mem_univ _
      simp at hm5
      rcases hm5 with hm5a | hm5b
      · exact hnd.2.1 hm5a.symm
      · exact hnd.2.2 hm5b.symm
    have h_makespan_ge_seven : (7 : ℝ) ≤ makespan 2 loads5 := by
      rcases h_dup with (h34 | h35 | h45)
      · have hbase : loads2 m3 = (3 : ℝ) := h_all_three m3
        have h_loads3_m3 : loads3 m3 = (5 : ℝ) := by
          have hm3_def : alg loads2 (2 : ℝ) = m3 := by rfl
          dsimp [loads3, step]
          rw [hm3_def]
          simp [hbase]
          norm_num
        have h_loads4_m3 : loads4 m3 = (7 : ℝ) := by
          have hm4_def : alg loads3 (2 : ℝ) = m3 := by simpa [m4] using h34.symm
          dsimp [loads4, step]
          rw [hm4_def]
          simp [h_loads3_m3]
          norm_num
        have h_l : (7 : ℝ) ≤ loads5 m3 := by
          have h_le : loads4 m3 ≤ loads5 m3 := by
            dsimp [loads5, step]
            split_ifs <;> nlinarith [h_loads4_m3]
          nlinarith
        have h := makespan_ge_each (m := 2) loads5 m3
        nlinarith
      · have hbase : loads2 m3 = (3 : ℝ) := h_all_three m3
        have h_loads3_m3 : loads3 m3 = (5 : ℝ) := by
          have hm3_def : alg loads2 (2 : ℝ) = m3 := by rfl
          dsimp [loads3, step]
          rw [hm3_def]
          simp [hbase]
          norm_num
        have h_l : (7 : ℝ) ≤ loads5 m3 := by
          have hm5_def : alg loads4 (2 : ℝ) = m3 := by simpa [m5] using h35.symm
          have h_le4 : (5 : ℝ) ≤ loads4 m3 := by
            dsimp [loads4, step]
            split_ifs <;> nlinarith [h_loads3_m3]
          dsimp [loads5, step]
          rw [hm5_def]
          simp
          nlinarith
        have h := makespan_ge_each (m := 2) loads5 m3
        nlinarith
      · have hbase : loads2 m4 = (3 : ℝ) := h_all_three m4
        have h3 : (3 : ℝ) ≤ loads3 m4 := by
          dsimp [loads3, step]
          split_ifs <;> nlinarith [hbase]
        have h_le4 : (5 : ℝ) ≤ loads4 m4 := by
          have hm4_def : alg loads3 (2 : ℝ) = m4 := by rfl
          dsimp [loads4, step]
          rw [hm4_def]
          simp
          nlinarith [h3]
        have h_l : (7 : ℝ) ≤ loads5 m4 := by
          have hm5_def : alg loads4 (2 : ℝ) = m4 := by simpa [m5] using h45.symm
          dsimp [loads5, step]
          rw [hm5_def]
          simp
          nlinarith
        have h := makespan_ge_each (m := 2) loads5 m4
        nlinarith
    have h_opt_six : OPT [3, 3, 2, 2, 2] = (6 : ℝ) := by
      apply opt_eq_of_const_schedule (m := 2) [3, 3, 2, 2, 2] (6 : ℝ)
      norm_num [totalLoad]
    calc
      (7 / 6 : ℝ) * OPT [3, 3, 2, 2, 2] ≤ (7 / 6 : ℝ) * 6 :=
        mul_le_mul_of_nonneg_left h_opt_six.le (by norm_num)
      _ = 7 := by norm_num
      _ ≤ makespan 2 loads5 := h_makespan_ge_seven
      _ ≤ algorithmMakespan 2 alg [3, 3, 2, 2, 2] := by
        dsimp [algorithmMakespan]
        rw [h_runFinal]

/-! ### m=3: Lower Bound (1+√37)/6 ≈ 1.18046

  Adaptive adversary (Seiden, Sgall, Woeginger 2000):
  Let `c = (1+√37)/6` and `x = (7-3c)/6 ≈ 0.5764`, so `1-x ≈ 0.4236 ≥ 1/3`.

  1. Send `[x, x, 1-x]`.
     - Two `x`'s on one machine → stop at `[x, x]`: makespan ≥ 2x, OPT ≤ x, ratio ≥ 2 ≥ c.
     - `x` and `1-x` on one machine → stop at `[x, x, 1-x]`:
       makespan ≥ 1, OPT ≤ x, ratio ≥ 1/x ≥ c.
     - All three distinct → send the second `1-x`.
  2. Second `1-x`:
     - Joins an `x` → load 1: stop at `[x, x, 1-x, 1-x]`:
       OPT ≤ 2(1-x) and makespan ≥ 1, so ratio ≥ 1/(2(1-x)) = c.
     - Joins the `1-x` (load 2(1-x)) → send `[1/3, 1/3, 1/3]`:
       the full sequence has OPT ≤ 1; the heavy machine receiving any `1/3`
       reaches exactly `2(1-x) + 1/3 = c`, otherwise the three `1/3`'s land on
       the two `x`-machines, one of which receives at least two of them,
       reaching `x + 2/3 ≥ c`.
-/

noncomputable def dec3_c : ℝ := (1 + Real.sqrt 37) / 6

/-- The m=3 adversary parameter `x = (7 - 3c)/6 ≈ 0.5764`. -/
noncomputable def dec3_x : ℝ := (7 - 3 * dec3_c) / 6

/-- `0 < x`, where `x = (13 - √37)/12`. -/
private lemma dec3_x_pos : 0 < dec3_x := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `0 < c`. -/
private lemma dec3_c_pos : 0 < dec3_c := by
  dsimp [dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `c ≤ 2`. -/
private lemma dec3_c_le_two : dec3_c ≤ 2 := by
  dsimp [dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `c·x ≤ 1`, so `1/x ≥ c`. -/
private lemma dec3_c_mul_x_le_one : dec3_c * dec3_x ≤ 1 := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `c · 2(1-x) = 1`, i.e. `c = 1/(2(1-x))`. -/
private lemma dec3_c_mul_two_one_minus_x : dec3_c * (2 * (1 - dec3_x)) = 1 := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `2(1-x) + 1/3 = c`. -/
private lemma dec3_two_one_minus_x_add_third : 2 * (1 - dec3_x) + 1 / 3 = dec3_c := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf

/-- `c ≤ x + 2/3`. -/
private lemma dec3_x_add_two_thirds_ge_c : dec3_c ≤ dec3_x + 2 / 3 := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `1-x ≤ x`, so the sequence `[x, x, 1-x]` is non-increasing. -/
private lemma dec3_one_minus_x_le_x : 1 - dec3_x ≤ dec3_x := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `x ≤ 2(1-x)`, used for the makespan of the packing schedule. -/
private lemma dec3_x_le_two_one_minus_x : dec3_x ≤ 2 * (1 - dec3_x) := by
  dsimp [dec3_x, dec3_c]
  have hsq : (Real.sqrt 37) ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg 37
  ring_nf
  nlinarith

/-- `OPT([x, x]) ≤ x`: pack the two `x`'s on separate machines. -/
private lemma dec3_opt_xx_le : OPT [dec3_x, dec3_x] ≤ dec3_x := by
  let loads : Loads 3 := fun i => if i = 0 then dec3_x else if i = 1 then dec3_x else 0
  have h_mk : makespan 3 loads ≤ dec3_x := by
    dsimp [makespan]
    exact Finset.sup'_le Finset.univ_nonempty (fun i => loads i) (by
      intro i hi
      fin_cases i <;> simp [loads] <;> nlinarith [dec3_x_pos])
  have h_total : totalLoad [dec3_x, dec3_x] = ∑ i : Fin 3, loads i := by
    simp [totalLoad]
    rw [Fin.sum_univ_three]
    simp [loads]
  exact le_trans (opt_le_of_schedule (m := 3) [dec3_x, dec3_x] loads h_total) h_mk

/-- `OPT([x, x, 1-x]) ≤ x`: pack the three jobs on separate machines. -/
private lemma dec3_opt_x_x_one_minus_x_le : OPT [dec3_x, dec3_x, 1 - dec3_x] ≤ dec3_x := by
  let loads : Loads 3 := fun i =>
    if i = 0 then dec3_x else if i = 1 then dec3_x else 1 - dec3_x
  have h_mk : makespan 3 loads ≤ dec3_x := by
    dsimp [makespan]
    exact Finset.sup'_le Finset.univ_nonempty (fun i => loads i) (by
      intro i hi
      fin_cases i <;> simp [loads] <;> nlinarith [dec3_one_minus_x_le_x])
  have h_total : totalLoad [dec3_x, dec3_x, 1 - dec3_x] = ∑ i : Fin 3, loads i := by
    simp [totalLoad]
    rw [Fin.sum_univ_three]
    simp [loads]
  exact le_trans (opt_le_of_schedule (m := 3) [dec3_x, dec3_x, 1 - dec3_x] loads h_total) h_mk

/-- `OPT([x, x, 1-x, 1-x]) ≤ 2(1-x)`: pack the two `1-x`'s together. -/
private lemma dec3_opt_x_x_one_minus_x_two_le :
    OPT [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] ≤ 2 * (1 - dec3_x) := by
  let loads : Loads 3 := fun i =>
    if i = 0 then dec3_x else if i = 1 then dec3_x else 2 * (1 - dec3_x)
  have h_mk : makespan 3 loads ≤ 2 * (1 - dec3_x) := by
    dsimp [makespan]
    exact Finset.sup'_le Finset.univ_nonempty (fun i => loads i) (by
      intro i hi
      fin_cases i <;> simp [loads] <;> nlinarith [dec3_x_le_two_one_minus_x])
  have h_total :
      totalLoad [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] = ∑ i : Fin 3, loads i := by
    simp [totalLoad]
    rw [Fin.sum_univ_three]
    simp [loads]
    ring
  exact le_trans
    (opt_le_of_schedule (m := 3) [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] loads h_total) h_mk

/-- `OPT([x, x, 1-x, 1-x, 1/3, 1/3, 1/3]) ≤ 1`: uniform load-one schedule. -/
private lemma dec3_opt_full_le :
    OPT [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3] ≤ 1 := by
  let loads : Loads 3 := fun _ => 1
  have h_mk : makespan 3 loads ≤ 1 := by
    dsimp [makespan]
    exact Finset.sup'_le Finset.univ_nonempty (fun i => loads i) (by
      intro i hi
      simp [loads])
  have h_total :
      totalLoad [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3] =
        ∑ i : Fin 3, loads i := by
    simp [totalLoad]
    rw [Fin.sum_univ_three]
    simp [loads]
    ring_nf
  exact le_trans
    (opt_le_of_schedule (m := 3) [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3]
      loads h_total) h_mk

/-- For `m = 3` machines with non-increasing job sizes, no deterministic online
    algorithm can have competitive ratio better than `(1+√37)/6 ≈ 1.18046`. -/
theorem dec3_lower_bound (alg : OnlineAlgorithm 3) :
    ∃ (sigma : JobSequence), algorithmMakespan 3 alg sigma ≥ dec3_c * OPT sigma := by
  let m1 : Fin 3 := alg (λ _ => 0) dec3_x
  let loads1 : Loads 3 := runAlgorithm 3 alg [dec3_x]
  let m2 : Fin 3 := alg loads1 dec3_x
  let loads2 : Loads 3 := runAlgorithm 3 alg [dec3_x, dec3_x]
  let m3 : Fin 3 := alg loads2 (1 - dec3_x)
  let loads3 : Loads 3 := runAlgorithm 3 alg [dec3_x, dec3_x, 1 - dec3_x]

  have h_loads1_m1 : loads1 m1 = dec3_x := by
    change (step (m := 3) alg (λ _ => 0) dec3_x) m1 = dec3_x
    dsimp [step]
    split_ifs with hif
    · simp
    · exfalso
      exact hif rfl

  by_cases h12 : m1 = m2
  · -- Two x's on one machine: stop at [x, x].
    use [dec3_x, dec3_x]
    have h_run2 : runAlgorithm 3 alg [dec3_x, dec3_x] = loads2 := by
      simp [runAlgorithm, loads1, loads2]
    have hm2_def : alg loads1 dec3_x = m1 := by exact h12.symm
    have h_loads2_m1 : loads2 m1 = 2 * dec3_x := by
      have h_run : loads2 = step (m := 3) alg loads1 dec3_x := by
        simp [loads2, runAlgorithm, loads1]
      rw [h_run]; dsimp [step]
      split_ifs with hif
      · simp [h_loads1_m1]
        ring
      · exfalso
        exact hif hm2_def.symm
    have h_mk : 2 * dec3_x ≤ algorithmMakespan 3 alg [dec3_x, dec3_x] := by
      dsimp [algorithmMakespan]
      rw [h_run2]
      have h := makespan_ge_each (m := 3) loads2 m1
      rw [h_loads2_m1] at h
      exact h
    calc
      dec3_c * OPT [dec3_x, dec3_x] ≤ dec3_c * dec3_x :=
        mul_le_mul_of_nonneg_left dec3_opt_xx_le dec3_c_pos.le
      _ ≤ 2 * dec3_x := by nlinarith [dec3_c_le_two, dec3_x_pos]
      _ ≤ algorithmMakespan 3 alg [dec3_x, dec3_x] := h_mk

  · have h12' : m1 ≠ m2 := h12
    by_cases h3x : m3 = m1 ∨ m3 = m2
    · -- x and 1-x on one machine: stop at [x, x, 1-x].
      use [dec3_x, dec3_x, 1 - dec3_x]
      have h_run2 : loads2 = step (m := 3) alg loads1 dec3_x := by
        simp [loads2, runAlgorithm, loads1]
      have hm2_def : alg loads1 dec3_x = m2 := by rfl
      have h_loads2_m1 : loads2 m1 = dec3_x := by
        rw [h_run2]; dsimp [step]
        split_ifs with hif
        · exfalso
          exact h12 (by simpa [hm2_def] using hif)
        · simp [h_loads1_m1]
      have h_loads2_m2 : loads2 m2 = dec3_x := by
        have h_loads1_m2 : loads1 m2 = 0 := by
          change (step (m := 3) alg (λ _ => 0) dec3_x) m2 = 0
          dsimp [step]
          split_ifs with hif
          · exfalso
            exact h12 (by simpa [m1] using hif.symm)
          · simp
        rw [h_run2]; dsimp [step]
        split_ifs with hif
        · simp [h_loads1_m2]
        · exfalso
          exact hif rfl
      have h_run3 : runAlgorithm 3 alg [dec3_x, dec3_x, 1 - dec3_x] = loads3 := by
        simp [runAlgorithm, loads1, loads2, loads3]
      have h_loads3_m3 : loads3 m3 = 1 := by
        have h_run3' : loads3 = step (m := 3) alg loads2 (1 - dec3_x) := by
          simp [loads3, runAlgorithm, loads1, loads2]
        rw [h_run3']; dsimp [step]
        split_ifs with hif
        · rcases h3x with h3a | h3b
          · simp [h3a, h_loads2_m1]
          · simp [h3b, h_loads2_m2]
        · exfalso
          exact hif rfl
      have h_mk : (1 : ℝ) ≤ algorithmMakespan 3 alg [dec3_x, dec3_x, 1 - dec3_x] := by
        dsimp [algorithmMakespan]
        rw [h_run3]
        have h := makespan_ge_each (m := 3) loads3 m3
        rw [h_loads3_m3] at h
        exact h
      calc
        dec3_c * OPT [dec3_x, dec3_x, 1 - dec3_x] ≤ dec3_c * dec3_x :=
          mul_le_mul_of_nonneg_left dec3_opt_x_x_one_minus_x_le dec3_c_pos.le
        _ ≤ 1 := dec3_c_mul_x_le_one
        _ ≤ algorithmMakespan 3 alg [dec3_x, dec3_x, 1 - dec3_x] := h_mk

    · -- All three of [x, x, 1-x] on distinct machines.
      have h13 : m3 ≠ m1 := by
        intro h
        exact h3x (Or.inl h)
      have h23 : m3 ≠ m2 := by
        intro h
        exact h3x (Or.inr h)
      have h_run2 : loads2 = step (m := 3) alg loads1 dec3_x := by
        simp [loads2, runAlgorithm, loads1]
      have hm2_def : alg loads1 dec3_x = m2 := by rfl
      have h_loads2_m1 : loads2 m1 = dec3_x := by
        rw [h_run2]; dsimp [step]
        split_ifs with hif
        · exfalso
          exact h12 (by simpa [hm2_def] using hif)
        · simp [h_loads1_m1]
      have h_loads2_m2 : loads2 m2 = dec3_x := by
        have h_loads1_m2 : loads1 m2 = 0 := by
          change (step (m := 3) alg (λ _ => 0) dec3_x) m2 = 0
          dsimp [step]
          split_ifs with hif
          · exfalso
            exact h12 (by simpa [m1] using hif.symm)
          · simp
        rw [h_run2]; dsimp [step]
        split_ifs with hif
        · simp [h_loads1_m2]
        · exfalso
          exact hif rfl
      have h_run3' : loads3 = step (m := 3) alg loads2 (1 - dec3_x) := by
        simp [loads3, runAlgorithm, loads1, loads2]
      have h_loads3_m1 : loads3 m1 = dec3_x := by
        rw [h_run3']; dsimp [step]
        split_ifs with hif
        · exfalso
          exact h13 (by simpa using hif.symm)
        · simp [h_loads2_m1]
      have h_loads3_m2 : loads3 m2 = dec3_x := by
        rw [h_run3']; dsimp [step]
        split_ifs with hif
        · exfalso
          exact h23 (by simpa using hif.symm)
        · simp [h_loads2_m2]
      have h_loads3_m3 : loads3 m3 = 1 - dec3_x := by
        have h_loads2_m3 : loads2 m3 = 0 := by
          rw [h_run2]; dsimp [step]
          have hm1_def : alg (λ _ : Fin 3 => 0) dec3_x = m1 := by rfl
          have hneq2 : m3 ≠ alg loads1 dec3_x := by
            intro h
            exact h23 (by simpa [hm2_def] using h)
          have h_loads1_m3 : loads1 m3 = 0 := by
            change (step (m := 3) alg (λ _ => 0) dec3_x) m3 = 0
            dsimp [step]
            have hneq1 : m3 ≠ alg (λ _ : Fin 3 => 0) dec3_x := by
              intro h
              exact h13 (by simpa [hm1_def] using h)
            simp [hneq1]
          simp [hneq2, h_loads1_m3]
        rw [h_run3']; dsimp [step]
        split_ifs with hif
        · simp [h_loads2_m3]
        · exfalso
          exact hif rfl
      let m4 : Fin 3 := alg loads3 (1 - dec3_x)
      let loads4 : Loads 3 := step (m := 3) alg loads3 (1 - dec3_x)
      by_cases h4x : m4 = m1 ∨ m4 = m2
      · -- Second 1-x joins an x: stop at [x, x, 1-x, 1-x].
        use [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x]
        have h_loads3_m4 : loads3 m4 = dec3_x := by
          rcases h4x with h4a | h4b
          · simpa [h4a] using h_loads3_m1
          · simpa [h4b] using h_loads3_m2
        have h_loads4_m4 : loads4 m4 = 1 := by
          dsimp [loads4, step]
          split_ifs with hif
          · simp [h_loads3_m4]
          · exfalso
            exact hif rfl
        have h_run4 : runAlgorithm 3 alg [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] = loads4 := by
          simp [runAlgorithm, loads1, loads2, loads3, loads4]
        have h_mk : (1 : ℝ) ≤ algorithmMakespan 3 alg [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] := by
          dsimp [algorithmMakespan]
          rw [h_run4]
          have h := makespan_ge_each (m := 3) loads4 m4
          rw [h_loads4_m4] at h
          exact h
        calc
          dec3_c * OPT [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x]
              ≤ dec3_c * (2 * (1 - dec3_x)) :=
                mul_le_mul_of_nonneg_left dec3_opt_x_x_one_minus_x_two_le dec3_c_pos.le
          _ = 1 := dec3_c_mul_two_one_minus_x
          _ ≤ algorithmMakespan 3 alg [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x] := h_mk

      · -- Second 1-x joins the 1-x: send [1/3, 1/3, 1/3].
        have h4x_neg : m4 ≠ m1 ∧ m4 ≠ m2 := by
          constructor
          · intro h
            exact h4x (Or.inl h)
          · intro h
            exact h4x (Or.inr h)
        have h_cov : ∀ j : Fin 3, j = m1 ∨ j = m2 ∨ j = m3 := by
          intro j
          have hset : ({m1, m2, m3} : Finset (Fin 3)) = Finset.univ := by
            apply Finset.eq_of_subset_of_card_le
            · exact Finset.subset_univ _
            · rw [Finset.card_univ, Fintype.card_fin]
              have hcard : ({m1, m2, m3} : Finset (Fin 3)).card = 3 := by
                rw [Finset.card_insert_of_notMem (by
                  intro h
                  simp at h
                  rcases h with h | h
                  · exact h12 h
                  · exact h13 h.symm)]
                rw [Finset.card_insert_of_notMem (by
                  intro h
                  have hm2_eq_m3 : m2 = m3 := by simpa using h
                  exact h23 hm2_eq_m3.symm)]
                simp
              rw [hcard]
          have hmem : j ∈ ({m1, m2, m3} : Finset (Fin 3)) := by
            rw [hset]; exact Finset.mem_univ j
          simpa using hmem
        have h4 : m4 = m3 := by
          rcases h_cov m4 with h | h | h
          · exact False.elim (h4x_neg.1 h)
          · exact False.elim (h4x_neg.2 h)
          · exact h
        have h_loads4_m3 : loads4 m3 = 2 * (1 - dec3_x) := by
          have hm4_def : alg loads3 (1 - dec3_x) = m3 := by simpa [m4] using h4
          dsimp [loads4, step]
          rw [hm4_def]
          split_ifs with hif
          · simp [h_loads3_m3]
            ring
          · exfalso
            exact hif rfl
        have h_loads4_other : ∀ j : Fin 3, j ≠ m3 → loads4 j = dec3_x := by
          intro j hj
          rcases h_cov j with hj1 | hj2 | hj3
          · rw [hj1]
            have hm4_def : alg loads3 (1 - dec3_x) = m3 := by simpa [m4] using h4
            dsimp [loads4, step]
            split_ifs with hif
            · exfalso
              have : m1 = m3 := by simpa [hm4_def] using hif
              exact h13 this.symm
            · simp [h_loads3_m1]
          · rw [hj2]
            have hm4_def : alg loads3 (1 - dec3_x) = m3 := by simpa [m4] using h4
            dsimp [loads4, step]
            split_ifs with hif
            · exfalso
              have : m2 = m3 := by simpa [hm4_def] using hif
              exact h23 this.symm
            · simp [h_loads3_m2]
          · exact False.elim (hj hj3)
        let m5 : Fin 3 := alg loads4 (1 / 3 : ℝ)
        let loads5 : Loads 3 := step (m := 3) alg loads4 (1 / 3 : ℝ)
        let m6 : Fin 3 := alg loads5 (1 / 3 : ℝ)
        let loads6 : Loads 3 := step (m := 3) alg loads5 (1 / 3 : ℝ)
        let m7 : Fin 3 := alg loads6 (1 / 3 : ℝ)
        let loads7 : Loads 3 := step (m := 3) alg loads6 (1 / 3 : ℝ)
        use [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3]
        have h_runFinal :
            runAlgorithm 3 alg [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3] =
              loads7 := by
          simp [runAlgorithm, loads1, loads2, loads3, loads4, loads5, loads6, loads7]
        have h_opt :
            OPT [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3] ≤ 1 :=
          dec3_opt_full_le
        have h_mk7 : dec3_c ≤ makespan 3 loads7 := by
          by_cases h_heavy : m5 = m3 ∨ m6 = m3 ∨ m7 = m3
          · rcases h_heavy with h5 | h6 | h7
            · have h_loads5_m3 : 2 * (1 - dec3_x) + 1 / 3 ≤ loads5 m3 := by
                have hm5_def : alg loads4 (1 / 3 : ℝ) = m3 := by simpa [m5] using h5
                dsimp [loads5, step]
                rw [hm5_def]
                simp [h_loads4_m3]
              have h_l : 2 * (1 - dec3_x) + 1 / 3 ≤ loads7 m3 := by
                have h_le : loads5 m3 ≤ loads7 m3 := by
                  dsimp [loads7, loads6, step]
                  split_ifs <;> nlinarith [h_loads5_m3]
                nlinarith
              have h := makespan_ge_each (m := 3) loads7 m3
              rw [← dec3_two_one_minus_x_add_third]
              exact le_trans h_l h
            · have h_base : loads4 m3 ≤ loads5 m3 := by
                dsimp [loads5, step]
                split_ifs <;> nlinarith [h_loads4_m3]
              have h_l6 : 2 * (1 - dec3_x) + 1 / 3 ≤ loads6 m3 := by
                have hm6_def : alg loads5 (1 / 3 : ℝ) = m3 := by simpa [m6] using h6
                dsimp [loads6, step]
                rw [hm6_def]
                simp
                nlinarith [h_base]
              have h_l : 2 * (1 - dec3_x) + 1 / 3 ≤ loads7 m3 := by
                have h_le : loads6 m3 ≤ loads7 m3 := by
                  dsimp [loads7, step]
                  split_ifs <;> nlinarith [h_l6]
                nlinarith
              have h := makespan_ge_each (m := 3) loads7 m3
              rw [← dec3_two_one_minus_x_add_third]
              exact le_trans h_l h
            · have h_base : loads4 m3 ≤ loads6 m3 := by
                dsimp [loads6, loads5, step]
                split_ifs <;> nlinarith [h_loads4_m3]
              have h_l : 2 * (1 - dec3_x) + 1 / 3 ≤ loads7 m3 := by
                have hm7_def : alg loads6 (1 / 3 : ℝ) = m3 := by simpa [m7] using h7
                dsimp [loads7, step]
                rw [hm7_def]
                simp
                nlinarith [h_base]
              have h := makespan_ge_each (m := 3) loads7 m3
              rw [← dec3_two_one_minus_x_add_third]
              exact le_trans h_l h
          · have h5n : m5 ≠ m3 := by
              intro h
              exact h_heavy (Or.inl h)
            have h6n : m6 ≠ m3 := by
              intro h
              exact h_heavy (Or.inr (Or.inl h))
            have h7n : m7 ≠ m3 := by
              intro h
              exact h_heavy (Or.inr (Or.inr h))
            have h_dup : m5 = m6 ∨ m5 = m7 ∨ m6 = m7 := by
              have hm5 : m5 = m1 ∨ m5 = m2 := by
                rcases h_cov m5 with h | h | h
                · exact Or.inl h
                · exact Or.inr h
                · exact False.elim (h5n h)
              have hm6 : m6 = m1 ∨ m6 = m2 := by
                rcases h_cov m6 with h | h | h
                · exact Or.inl h
                · exact Or.inr h
                · exact False.elim (h6n h)
              have hm7 : m7 = m1 ∨ m7 = m2 := by
                rcases h_cov m7 with h | h | h
                · exact Or.inl h
                · exact Or.inr h
                · exact False.elim (h7n h)
              rcases hm5 with hm5a | hm5b <;> rcases hm6 with hm6a | hm6b <;>
                rcases hm7 with hm7a | hm7b
              · exact Or.inl (hm5a.trans hm6a.symm)
              · exact Or.inl (hm5a.trans hm6a.symm)
              · exact Or.inr (Or.inl (hm5a.trans hm7a.symm))
              · exact Or.inr (Or.inr (hm6b.trans hm7b.symm))
              · exact Or.inr (Or.inr (hm6a.trans hm7a.symm))
              · exact Or.inr (Or.inl (hm5b.trans hm7b.symm))
              · exact Or.inl (hm5b.trans hm6b.symm)
              · exact Or.inl (hm5b.trans hm6b.symm)
            rcases h_dup with h56 | h57 | h67
            · have hbase : loads4 m5 = dec3_x := h_loads4_other m5 h5n
              have h_loads5_m5 : dec3_x + 1 / 3 ≤ loads5 m5 := by
                have hm5_def : alg loads4 (1 / 3 : ℝ) = m5 := by rfl
                dsimp [loads5, step]
                rw [hm5_def]
                simp [hbase]
              have h_l : dec3_x + 2 / 3 ≤ loads7 m5 := by
                have hm6_def : alg loads5 (1 / 3 : ℝ) = m5 := by simpa [m6] using h56.symm
                have h_loads6_m5 : dec3_x + 2 / 3 ≤ loads6 m5 := by
                  dsimp [loads6, step]
                  rw [hm6_def]
                  simp
                  linarith [h_loads5_m5]
                have h_le : loads6 m5 ≤ loads7 m5 := by
                  dsimp [loads7, step]
                  split_ifs <;> linarith [h_loads6_m5]
                linarith
              have h := makespan_ge_each (m := 3) loads7 m5
              exact le_trans (le_trans dec3_x_add_two_thirds_ge_c h_l) h
            · have hbase : loads4 m5 = dec3_x := h_loads4_other m5 h5n
              have h_loads5_m5 : dec3_x + 1 / 3 ≤ loads5 m5 := by
                have hm5_def : alg loads4 (1 / 3 : ℝ) = m5 := by rfl
                dsimp [loads5, step]
                rw [hm5_def]
                simp [hbase]
              have h_l : dec3_x + 2 / 3 ≤ loads7 m5 := by
                have hm7_def : alg loads6 (1 / 3 : ℝ) = m5 := by simpa [m7] using h57.symm
                have h_le : loads5 m5 ≤ loads6 m5 := by
                  dsimp [loads6, step]
                  split_ifs <;> linarith [h_loads5_m5]
                dsimp [loads7, step]
                rw [hm7_def]
                simp
                linarith
              have h := makespan_ge_each (m := 3) loads7 m5
              exact le_trans (le_trans dec3_x_add_two_thirds_ge_c h_l) h
            · have hbase : loads4 m6 = dec3_x := h_loads4_other m6 h6n
              have h_loads6_m6 : dec3_x + 1 / 3 ≤ loads6 m6 := by
                have hm6_def : alg loads5 (1 / 3 : ℝ) = m6 := by rfl
                have h_le5 : loads4 m6 ≤ loads5 m6 := by
                  dsimp [loads5, step]
                  split_ifs <;> linarith [hbase]
                dsimp [loads6, step]
                rw [hm6_def]
                simp
                linarith
              have h_l : dec3_x + 2 / 3 ≤ loads7 m6 := by
                have hm7_def : alg loads6 (1 / 3 : ℝ) = m6 := by simpa [m7] using h67.symm
                dsimp [loads7, step]
                rw [hm7_def]
                simp
                linarith [h_loads6_m6]
              have h := makespan_ge_each (m := 3) loads7 m6
              exact le_trans (le_trans dec3_x_add_two_thirds_ge_c h_l) h
        calc
          dec3_c * OPT [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3]
              ≤ dec3_c * 1 := mul_le_mul_of_nonneg_left h_opt dec3_c_pos.le
          _ = dec3_c := by ring
          _ ≤ makespan 3 loads7 := h_mk7
          _ ≤ algorithmMakespan 3 alg
              [dec3_x, dec3_x, 1 - dec3_x, 1 - dec3_x, 1 / 3, 1 / 3, 1 / 3] := by
            dsimp [algorithmMakespan]
            rw [h_runFinal]

end OnlineScheduling
