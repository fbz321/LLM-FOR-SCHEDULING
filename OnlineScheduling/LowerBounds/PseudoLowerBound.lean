/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Pseudo Lower Bounds (Tan & Li, 2015), m = 4

For 4 machines, using only the weak lower bounds
`LB1 = totalLoad / m` and `LB2 = maxJobSize` on the optimum makespan,
no online algorithm can be proved to have competitive ratio below
`1 + gamma4 = 26/15`.

Adaptive adversary (`gamma = 11/15`, `q = 1`):
  Phase 1: 4 jobs of `a = (1-gamma)(gamma-1/2) = 14/225`
  Phase 2: 4 jobs of `b = gamma(gamma-1/2) = 77/450`
  Phase 3: 3 jobs of `1/2`
  Phase 4: 1 job of `d = (3-gamma)/4 = 17/30`
  Phase 5: 1 job of `1`
Stop at the first phase where two jobs collide; otherwise keep going.
In every stopping prefix `sigma`, the makespan is at least
`(1+gamma) * max (totalLoad sigma / 4) (maxJobSize sigma)`.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset

namespace OnlineScheduling

noncomputable def gamma4 : ℝ := 11 / 15
noncomputable def a4 : ℝ := (1 - gamma4) * (gamma4 - 1 / 2)
noncomputable def b4 : ℝ := gamma4 * (gamma4 - 1 / 2)
noncomputable def d4 : ℝ := (3 - gamma4) / 4

private lemma a4_eq : a4 = 14 / 225 := by norm_num [a4, gamma4]
private lemma b4_eq : b4 = 77 / 450 := by norm_num [b4, gamma4]
private lemma d4_eq : d4 = 17 / 30 := by norm_num [d4, gamma4]
private lemma gamma4_pos : 0 < gamma4 := by norm_num [gamma4]
private lemma a4_pos : 0 < a4 := by norm_num [a4, gamma4]
private lemma b4_pos : 0 < b4 := by norm_num [b4, gamma4]

/-- The weak pseudo lower bound: `max` of average load and largest job. -/
noncomputable def PseudoLB (sigma : JobSequence) : ℝ :=
  max (totalLoad sigma / 4) (maxJobSize sigma)

private lemma gamma4_le_one : gamma4 ≤ 1 := by norm_num [gamma4]

/-- `a4 + 2*b4 = (1+gamma4)(gamma4 - 1/2)`, the Phase-2 collision bound. -/
private lemma a4_add_two_b4_eq : a4 + 2 * b4 = (1 + gamma4) * (gamma4 - 1 / 2) := by
  rw [a4_eq, b4_eq]
  norm_num [gamma4]

/-- `gamma4 + d4 = (1+gamma4) * (3/4)`, the Phase-4 collision bound. -/
private lemma gamma4_add_d4_eq : gamma4 + d4 = (1 + gamma4) * (3 / 4) := by
  rw [d4_eq]
  norm_num [gamma4]

/-- `gamma4 + 1 = (1+gamma4) * 1`, the Phase-5 bound. -/
private lemma gamma4_add_one_eq : gamma4 + 1 = (1 + gamma4) * 1 := by ring

/-- Phase-3 collision makespan `gamma4 + 1/2` dominates `(1+gamma4)*73/120`. -/
private lemma phase3_bound : (1 + gamma4) * (73 / 120) ≤ gamma4 + 1 / 2 := by
  norm_num [gamma4]

/-- `a4 + b4 = gamma4 - 1/2`, the balanced load after Phases 1 and 2. -/
private lemma a4_add_b4_eq_gamma : a4 + b4 = gamma4 - 1 / 2 := by
  rw [a4_eq, b4_eq]
  norm_num [gamma4]

private lemma s1_pseudoLB : PseudoLB [a4, a4, a4, a4] = a4 := by
  dsimp [PseudoLB, totalLoad, maxJobSize]
  rw [a4_eq]
  norm_num

private lemma s2_pseudoLB : PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4] = gamma4 - 1 / 2 := by
  dsimp [PseudoLB, totalLoad, maxJobSize]
  rw [a4_eq, b4_eq]
  norm_num [gamma4]

private lemma s3_pseudoLB :
    PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2] = 73 / 120 := by
  dsimp [PseudoLB, totalLoad, maxJobSize]
  rw [a4_eq, b4_eq]
  norm_num [gamma4]

private lemma s4_pseudoLB :
    PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2, d4] = 3 / 4 := by
  dsimp [PseudoLB, totalLoad, maxJobSize]
  rw [a4_eq, b4_eq, d4_eq]
  norm_num [gamma4]

private lemma s5_pseudoLB :
    PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2, d4, 1] = 1 := by
  dsimp [PseudoLB, totalLoad, maxJobSize]
  rw [a4_eq, b4_eq, d4_eq]
  norm_num [gamma4]

/-- For 4 machines, using only the weak lower bounds on the optimum makespan,
    no online algorithm can be proved to have competitive ratio below `1 + 11/15`. -/
theorem m4_pseudo_lower_bound (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence, algorithmMakespan 4 alg sigma ≥ (1 + gamma4) * PseudoLB sigma := by
  let σ1 : JobSequence := List.replicate 4 a4
  have h_layer1 := layer_separation (m := 4) alg a4 a4_pos
  rcases h_layer1 with h_imbal1 | h_bal1
  · -- Two Phase-1 jobs on one machine: stop at σ1.
    use σ1
    have h_opt1 : OPT σ1 = a4 := opt_of_identical_jobs (m := 4) a4 a4_pos
    have hlb : PseudoLB σ1 = a4 := by
      change PseudoLB [a4, a4, a4, a4] = a4
      exact s1_pseudoLB
    calc
      (1 + gamma4) * PseudoLB σ1 = (1 + gamma4) * a4 := by rw [hlb]
      _ ≤ 2 * a4 := by nlinarith [gamma4_le_one, a4_pos]
      _ = 2 * OPT σ1 := by rw [h_opt1]
      _ ≤ algorithmMakespan 4 alg σ1 := h_imbal1

  · -- Phase 1 balanced: all loads = a4.
    let loads1 : Loads 4 := runAlgorithm 4 alg σ1
    have h_loads1 : ∀ i : Fin 4, loads1 i = a4 := h_bal1
    let σ2 : JobSequence := σ1 ++ List.replicate 4 b4
    have h_layer2 := layer_separation_from_base (m := 4) alg a4 b4 b4_pos loads1 h_loads1
    rcases h_layer2 with h_imbal2 | h_bal2
    · -- Two Phase-2 jobs collide: stop at σ2.
      use σ2
      have hlb : PseudoLB σ2 = gamma4 - 1 / 2 := by
        change PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4] = gamma4 - 1 / 2
        exact s2_pseudoLB
      have h_run2 : runAlgorithm 4 alg σ2 =
          (List.replicate 4 b4).foldl (step (m := 4) alg) loads1 := by
        simp [σ2, σ1, runAlgorithm, loads1]
      have h_mk : a4 + 2 * b4 ≤ algorithmMakespan 4 alg σ2 := by
        dsimp [algorithmMakespan]
        rw [h_run2]
        exact h_imbal2
      calc
        (1 + gamma4) * PseudoLB σ2 = (1 + gamma4) * (gamma4 - 1 / 2) := by rw [hlb]
        _ = a4 + 2 * b4 := a4_add_two_b4_eq.symm
        _ ≤ algorithmMakespan 4 alg σ2 := h_mk

    · -- Phase 2 balanced: all loads = a4 + b4 = gamma4 - 1/2.
      let loads2 : Loads 4 := runAlgorithm 4 alg σ2
      have h_run2 : loads2 = (List.replicate 4 b4).foldl (step (m := 4) alg) loads1 := by
        simp [loads2, σ2, σ1, runAlgorithm, loads1]
      have h_loads2 : ∀ i : Fin 4, loads2 i = a4 + b4 := by
        simpa [h_run2] using h_bal2
      -- Phase 3: three jobs of size 1/2.
      let m5 : Fin 4 := alg loads2 (1 / 2)
      let loads3 : Loads 4 := step (m := 4) alg loads2 (1 / 2)
      let m6 : Fin 4 := alg loads3 (1 / 2)
      let loads4 : Loads 4 := step (m := 4) alg loads3 (1 / 2)
      let m7 : Fin 4 := alg loads4 (1 / 2)
      let loads5 : Loads 4 := step (m := 4) alg loads4 (1 / 2)
      let σ3 : JobSequence := σ2 ++ [1 / 2, 1 / 2, 1 / 2]
      have h_run3 : runAlgorithm 4 alg σ3 = loads5 := by
        simp [σ3, σ2, σ1, runAlgorithm, loads1, loads2, loads3, loads4, loads5]
      by_cases h_coll3 : m5 = m6 ∨ m5 = m7 ∨ m6 = m7
      · -- Two Phase-3 jobs collide: stop at σ3.
        use σ3
        have hlb : PseudoLB σ3 = 73 / 120 := by
          change PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2] = 73 / 120
          exact s3_pseudoLB
        have h_mk : gamma4 + 1 / 2 ≤ algorithmMakespan 4 alg σ3 := by
          dsimp [algorithmMakespan]
          rw [h_run3]
          rcases h_coll3 with h56 | h57 | h67
          · -- m5 = m6
            have h_loads3_m5 : loads3 m5 = a4 + b4 + 1 / 2 := by
              dsimp [loads3, step]
              split_ifs with hif
              · simp [h_loads2 m5]
              · exfalso
                exact hif rfl
            have h_loads4_m5 : loads4 m5 = a4 + b4 + 1 := by
              have hm6_def : alg loads3 (1 / 2) = m5 := by simpa [m6] using h56.symm
              dsimp [loads4, step]
              rw [hm6_def]
              split_ifs with hif
              · nlinarith [h_loads3_m5]
              · exfalso
                exact hif rfl
            have h_l : gamma4 + 1 / 2 ≤ loads5 m5 := by
              have h_le : loads4 m5 ≤ loads5 m5 := by
                dsimp [loads5, step]
                split_ifs <;> linarith [h_loads4_m5]
              nlinarith [a4_add_b4_eq_gamma, h_loads4_m5, h_le]
            have h := makespan_ge_each (m := 4) loads5 m5
            nlinarith
          · -- m5 = m7
            have h_loads3_m5 : loads3 m5 = a4 + b4 + 1 / 2 := by
              dsimp [loads3, step]
              split_ifs with hif
              · simp [h_loads2 m5]
              · exfalso
                exact hif rfl
            have h_loads5_m5 : loads5 m5 ≥ a4 + b4 + 1 := by
              have hm7_def : alg loads4 (1 / 2) = m5 := by simpa [m7] using h57.symm
              have h_le4 : loads3 m5 ≤ loads4 m5 := by
                dsimp [loads4, step]
                split_ifs <;> linarith [h_loads3_m5]
              dsimp [loads5, step]
              rw [hm7_def]
              simp
              nlinarith [h_le4, h_loads3_m5]
            have h_l : gamma4 + 1 / 2 ≤ loads5 m5 := by
              nlinarith [a4_add_b4_eq_gamma, h_loads5_m5]
            have h := makespan_ge_each (m := 4) loads5 m5
            nlinarith
          · -- m6 = m7
            have h_loads3_m6_ge : a4 + b4 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h_loads5_m6 : a4 + b4 + 1 ≤ loads5 m6 := by
              have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
              have hm7_def : alg loads4 (1 / 2) = m6 := by simpa [m7] using h67.symm
              have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                dsimp [loads4, step]
                rw [hm6_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              have h5 : loads5 m6 = loads4 m6 + 1 / 2 := by
                dsimp [loads5, step]
                rw [hm7_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              nlinarith [h_loads3_m6_ge, h4, h5]
            have h_l : gamma4 + 1 / 2 ≤ loads5 m6 := by
              nlinarith [a4_add_b4_eq_gamma, h_loads5_m6]
            have h := makespan_ge_each (m := 4) loads5 m6
            nlinarith
        calc
          (1 + gamma4) * PseudoLB σ3 = (1 + gamma4) * (73 / 120) := by rw [hlb]
          _ ≤ gamma4 + 1 / 2 := phase3_bound
          _ ≤ algorithmMakespan 4 alg σ3 := h_mk

      · -- Phase 3 jobs on distinct machines.
        have h56 : m5 ≠ m6 := by
          intro h
          exact h_coll3 (Or.inl h)
        have h57 : m5 ≠ m7 := by
          intro h
          exact h_coll3 (Or.inr (Or.inl h))
        have h67 : m6 ≠ m7 := by
          intro h
          exact h_coll3 (Or.inr (Or.inr h))
        -- Phase 4: one job of size d4.
        let m8 : Fin 4 := alg loads5 d4
        let loads6 : Loads 4 := step (m := 4) alg loads5 d4
        let σ4 : JobSequence := σ3 ++ [d4]
        have h_run4 : runAlgorithm 4 alg σ4 = loads6 := by
          simp [σ4, σ3, runAlgorithm, loads1, loads2, loads3, loads4, loads5, loads6]
        by_cases h4 : m8 = m5 ∨ m8 = m6 ∨ m8 = m7
        · -- Phase-4 job joins a Phase-3 machine: stop at σ4.
          use σ4
          have hlb : PseudoLB σ4 = 3 / 4 := by
            change PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2, d4] = 3 / 4
            exact s4_pseudoLB
          have h_mk : gamma4 + d4 ≤ algorithmMakespan 4 alg σ4 := by
            dsimp [algorithmMakespan]
            rw [h_run4]
            -- m8 has load gamma4 (from phase 3) and receives d4
            have h_loads5_m8 : a4 + b4 + 1 / 2 ≤ loads5 m8 := by
              rcases h4 with h8 | h8 | h8
              · rw [h8]
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a4 + b4 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have hle : loads3 m5 ≤ loads5 m5 := by
                  dsimp [loads5, loads4, step]
                  split_ifs <;> nlinarith [h3]
                nlinarith [h3, hle]
              · rw [h8]
                have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                have h3 : loads3 m6 = a4 + b4 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m6 = m5 := by simpa [← hm5_def] using hif
                    exact h56 this.symm
                  · simp [h_loads2 m6]
                have h4_ge : loads4 m6 = a4 + b4 + 1 / 2 := by
                  dsimp [loads4, step]
                  rw [hm6_def]
                  split_ifs with hif
                  · simp [h3]
                  · exfalso
                    exact hif rfl
                have hle : loads4 m6 ≤ loads5 m6 := by
                  dsimp [loads5, step]
                  split_ifs <;> nlinarith [h4_ge]
                nlinarith [h4_ge, hle]
              · rw [h8]
                have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                have h3 : loads3 m7 = a4 + b4 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m7 = m5 := by simpa [← hm5_def] using hif
                    exact h57 this.symm
                  · simp [h_loads2 m7]
                have h4_ge : loads4 m7 = a4 + b4 := by
                  dsimp [loads4, step]
                  split_ifs with hif
                  · exfalso
                    have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                    have : m7 = m6 := by simpa [← hm6_def] using hif
                    exact h67 this.symm
                  · simp [h3]
                have h5_ge : a4 + b4 + 1 / 2 ≤ loads5 m7 := by
                  dsimp [loads5, step]
                  rw [hm7_def]
                  split_ifs with hif
                  · nlinarith [h4_ge]
                  · exfalso
                    exact hif rfl
                exact h5_ge
            have h_loads6_m8 : a4 + b4 + 1 / 2 + d4 ≤ loads6 m8 := by
              have hm8_def : alg loads5 d4 = m8 := by rfl
              dsimp [loads6, step]
              rw [hm8_def]
              split_ifs with hif
              · nlinarith [h_loads5_m8]
              · exfalso
                exact hif rfl
            have h := makespan_ge_each (m := 4) loads6 m8
            nlinarith [a4_add_b4_eq_gamma, h_loads6_m8, h]
          calc
            (1 + gamma4) * PseudoLB σ4 = (1 + gamma4) * (3 / 4) := by rw [hlb]
            _ = gamma4 + d4 := gamma4_add_d4_eq.symm
            _ ≤ algorithmMakespan 4 alg σ4 := h_mk

        · -- Phase-4 job joins the untouched machine: all loads ≥ gamma4.
          have h8n : m8 ≠ m5 := by
            intro h
            exact h4 (Or.inl h)
          have h8n6 : m8 ≠ m6 := by
            intro h
            exact h4 (Or.inr (Or.inl h))
          have h8n7 : m8 ≠ m7 := by
            intro h
            exact h4 (Or.inr (Or.inr h))
          -- Phase 5: one job of size 1.
          let m9 : Fin 4 := alg loads6 (1 : ℝ)
          let loads7 : Loads 4 := step (m := 4) alg loads6 (1 : ℝ)
          let σ5 : JobSequence := σ4 ++ [1]
          use σ5
          have h_run5 : runAlgorithm 4 alg σ5 = loads7 := by
            dsimp [σ5]
            rw [runAlgorithm_append_singleton (m := 4) alg σ4 (1 : ℝ)]
            rw [h_run4]
          have hlb : PseudoLB σ5 = 1 := by
            change PseudoLB [a4, a4, a4, a4, b4, b4, b4, b4, 1 / 2, 1 / 2, 1 / 2, d4, 1] = 1
            exact s5_pseudoLB
          have h_mk : gamma4 + 1 ≤ algorithmMakespan 4 alg σ5 := by
            dsimp [algorithmMakespan]
            rw [h_run5]
            have h_loads7_m9 : loads7 m9 = loads6 m9 + 1 := by
              have hm9_def : alg loads6 (1 : ℝ) = m9 := by rfl
              dsimp [loads7, step]
              rw [hm9_def]
              split_ifs with hif
              · rfl
              · exfalso
                exact hif rfl
            -- every machine has load ≥ gamma4 after phase 4
            have h_all_ge : ∀ i : Fin 4, gamma4 ≤ loads6 i := by
              intro i
              have hcov : ({m5, m6, m7, m8} : Finset (Fin 4)) = Finset.univ := by
                apply Finset.eq_of_subset_of_card_le
                · exact Finset.subset_univ _
                · rw [Finset.card_univ, Fintype.card_fin]
                  have hcard : ({m5, m6, m7, m8} : Finset (Fin 4)).card = 4 := by
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h
                      · exact h56 h
                      · exact h57 h
                      · exact h8n h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h
                      · exact h67 h
                      · exact h8n6 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      exact h8n7 h.symm)]
                    simp
                  rw [hcard]
              have hmem : i ∈ ({m5, m6, m7, m8} : Finset (Fin 4)) := by
                rw [hcov]
                exact Finset.mem_univ i
              simp at hmem
              rcases hmem with rfl | rfl | rfl | rfl
              · -- i = m5: load = gamma4
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a4 + b4 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have h45 : loads4 m5 = loads3 m5 := by
                  dsimp [loads4, step]
                  split_ifs with hif
                  · exfalso
                    have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                    have : m5 = m6 := by simpa [← hm6_def] using hif
                    exact h56 this
                  · rfl
                have h5 : loads5 m5 = loads4 m5 := by
                  dsimp [loads5, step]
                  split_ifs with hif
                  · exfalso
                    have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                    have : m5 = m7 := by simpa [← hm7_def] using hif
                    exact h57 this
                  · rfl
                have h6 : loads6 m5 = loads5 m5 := by
                  dsimp [loads6, step]
                  split_ifs with hif
                  · exfalso
                    have hm8_def : alg loads5 d4 = m8 := by rfl
                    have : m5 = m8 := by simpa [← hm8_def] using hif
                    exact h8n this.symm
                  · rfl
                nlinarith [a4_add_b4_eq_gamma, h3, h45, h5, h6]
              · -- i = m6
                have h3 : loads3 m6 = a4 + b4 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m6 = m5 := by simpa [← hm5_def] using hif
                    exact h56 this.symm
                  · simp [h_loads2 m6]
                have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                  dsimp [loads4, step]
                  rw [hm6_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                have h5 : loads5 m6 = loads4 m6 := by
                  dsimp [loads5, step]
                  split_ifs with hif
                  · exfalso
                    have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                    have : m6 = m7 := by simpa [← hm7_def] using hif
                    exact h67 this
                  · rfl
                have h6 : loads6 m6 = loads5 m6 := by
                  dsimp [loads6, step]
                  split_ifs with hif
                  · exfalso
                    have hm8_def : alg loads5 d4 = m8 := by rfl
                    have : m6 = m8 := by simpa [← hm8_def] using hif
                    exact h8n6 this.symm
                  · rfl
                nlinarith [a4_add_b4_eq_gamma, h3, h4, h5, h6]
              · -- i = m7
                have h3 : loads3 m7 = a4 + b4 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m7 = m5 := by simpa [← hm5_def] using hif
                    exact h57 this.symm
                  · simp [h_loads2 m7]
                have h4 : loads4 m7 = loads3 m7 := by
                  dsimp [loads4, step]
                  split_ifs with hif
                  · exfalso
                    have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                    have : m7 = m6 := by simpa [← hm6_def] using hif
                    exact h67 this.symm
                  · rfl
                have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                have h5 : loads5 m7 = loads4 m7 + 1 / 2 := by
                  dsimp [loads5, step]
                  rw [hm7_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                have h6 : loads6 m7 = loads5 m7 := by
                  dsimp [loads6, step]
                  split_ifs with hif
                  · exfalso
                    have hm8_def : alg loads5 d4 = m8 := by rfl
                    have : m7 = m8 := by simpa [← hm8_def] using hif
                    exact h8n7 this.symm
                  · rfl
                nlinarith [a4_add_b4_eq_gamma, h3, h4, h5, h6]
              · -- i = m8: load = gamma4 - 1/2 + d4 ≥ gamma4
                have hm8_def : alg loads5 d4 = m8 := by rfl
                have h5 : loads5 m8 = a4 + b4 := by
                  have h3 : loads3 m8 = a4 + b4 := by
                    dsimp [loads3, step]
                    split_ifs with hif
                    · exfalso
                      have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                      have : m8 = m5 := by simpa [← hm5_def] using hif
                      exact h8n this
                    · simp [h_loads2 m8]
                  have h4 : loads4 m8 = loads3 m8 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m8 = m6 := by simpa [← hm6_def] using hif
                      exact h8n6 this
                    · rfl
                  have h45 : loads5 m8 = loads4 m8 := by
                    dsimp [loads5, step]
                    split_ifs with hif
                    · exfalso
                      have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                      have : m8 = m7 := by simpa [← hm7_def] using hif
                      exact h8n7 this
                    · rfl
                  nlinarith [h3, h4, h45]
                have h6 : gamma4 ≤ loads6 m8 := by
                  dsimp [loads6, step]
                  rw [hm8_def]
                  split_ifs with hif
                  · nlinarith [a4_add_b4_eq_gamma, h5, d4_eq]
                  · exfalso
                    exact hif rfl
                exact h6
            have h := makespan_ge_each (m := 4) loads7 m9
            rw [h_loads7_m9] at h
            nlinarith [h_all_ge m9, h]
          calc
            (1 + gamma4) * PseudoLB σ5 = (1 + gamma4) * 1 := by rw [hlb]
            _ = gamma4 + 1 := gamma4_add_one_eq.symm
            _ ≤ algorithmMakespan 4 alg σ5 := h_mk

end OnlineScheduling
