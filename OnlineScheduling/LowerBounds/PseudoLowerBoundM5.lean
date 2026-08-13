/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Pseudo Lower Bounds (Tan & Li, 2015), m = 5

For 5 machines, using only the weak lower bounds
`LB1 = totalLoad / m` and `LB2 = maxJobSize` on the optimum makespan,
no online algorithm can be proved to have competitive ratio below
`1 + gamma5 = 1 + 37/48`.

Adaptive adversary (`gamma = 37/48`, `q = 1`):
  Phase 1: 5 jobs of `a = (1-gamma)(gamma-1/2) = 143/2304`
  Phase 2: 5 jobs of `b = gamma(gamma-1/2) = 481/2304`
  Phase 3: 4 jobs of `1/2`
  Phase 4: 1 job of `d = (4-gamma)/5 = 31/48`
  Phase 5: 1 job of `1`
Stop at the first phase where two jobs collide; otherwise keep going.
In every stopping prefix `sigma`, the makespan is at least
`(1+gamma) * max (totalLoad sigma / 5) (maxJobSize sigma)`.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

set_option maxHeartbeats 800000

open Finset

namespace OnlineScheduling

noncomputable def gamma5 : ℝ := 37 / 48
noncomputable def a5 : ℝ := (1 - gamma5) * (gamma5 - 1 / 2)
noncomputable def b5 : ℝ := gamma5 * (gamma5 - 1 / 2)
noncomputable def d5 : ℝ := (4 - gamma5) / 5

private lemma a5_eq : a5 = 143 / 2304 := by norm_num [a5, gamma5]
private lemma b5_eq : b5 = 481 / 2304 := by norm_num [b5, gamma5]
private lemma d5_eq : d5 = 31 / 48 := by norm_num [d5, gamma5]
private lemma gamma5_pos : 0 < gamma5 := by norm_num [gamma5]
private lemma a5_pos : 0 < a5 := by norm_num [a5, gamma5]
private lemma b5_pos : 0 < b5 := by norm_num [b5, gamma5]
private lemma d5_pos : 0 < d5 := by norm_num [d5, gamma5]

/-- The weak pseudo lower bound: `max` of average load and largest job. -/
noncomputable def PseudoLB5 (sigma : JobSequence) : ℝ :=
  max (totalLoad sigma / 5) (maxJobSize sigma)

private lemma gamma5_le_one : gamma5 ≤ 1 := by norm_num [gamma5]

/-- `a5 + 2*b5 = (1+gamma5)(gamma5 - 1/2)`, the Phase-2 collision bound. -/
private lemma a5_add_two_b5_eq : a5 + 2 * b5 = (1 + gamma5) * (gamma5 - 1 / 2) := by
  rw [a5_eq, b5_eq]
  norm_num [gamma5]

/-- `gamma5 + d5 = (1+gamma5) * (4/5)`, the Phase-4 collision bound. -/
private lemma gamma5_add_d5_eq : gamma5 + d5 = (1 + gamma5) * (4 / 5) := by
  rw [d5_eq]
  norm_num [gamma5]

/-- `gamma5 + 1 = (1+gamma5) * 1`, the Phase-5 bound. -/
private lemma gamma5_add_one_eq : gamma5 + 1 = (1 + gamma5) * 1 := by ring

/-- Phase-3 collision makespan `gamma5 + 1/2` dominates `(1+gamma5)*161/240`. -/
private lemma phase3_bound : (1 + gamma5) * (161 / 240) ≤ gamma5 + 1 / 2 := by
  norm_num [gamma5]

/-- `a5 + b5 = gamma5 - 1/2`, the balanced load after Phases 1 and 2. -/
private lemma a5_add_b5_eq_gamma : a5 + b5 = gamma5 - 1 / 2 := by
  rw [a5_eq, b5_eq]
  norm_num [gamma5]

private lemma s1_pseudoLB : PseudoLB5 [a5, a5, a5, a5, a5] = a5 := by
  dsimp [PseudoLB5, totalLoad, maxJobSize]
  rw [a5_eq]
  norm_num

private lemma s2_pseudoLB :
    PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5] = gamma5 - 1 / 2 := by
  dsimp [PseudoLB5, totalLoad, maxJobSize]
  rw [a5_eq, b5_eq]
  norm_num [gamma5]

private lemma s3_pseudoLB :
    PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5, 1 / 2, 1 / 2, 1 / 2, 1 / 2] =
      161 / 240 := by
  dsimp [PseudoLB5, totalLoad, maxJobSize]
  rw [a5_eq, b5_eq]
  norm_num [gamma5]

private lemma s4_pseudoLB :
    PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d5] =
      4 / 5 := by
  dsimp [PseudoLB5, totalLoad, maxJobSize]
  rw [a5_eq, b5_eq, d5_eq]
  norm_num [gamma5]

private lemma s5_pseudoLB :
    PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d5, 1] = 1 := by
  dsimp [PseudoLB5, totalLoad, maxJobSize]
  rw [a5_eq, b5_eq, d5_eq]
  norm_num [gamma5]

/-- For 5 machines, using only the weak lower bounds on the optimum makespan,
    no online algorithm can be proved to have competitive ratio below `1 + 37/48`. -/
theorem m5_pseudo_lower_bound (alg : OnlineAlgorithm 5) :
    ∃ sigma : JobSequence, algorithmMakespan 5 alg sigma ≥ (1 + gamma5) * PseudoLB5 sigma := by
  let σ1 : JobSequence := List.replicate 5 a5
  have h_layer1 := layer_separation (m := 5) alg a5 a5_pos
  rcases h_layer1 with h_imbal1 | h_bal1
  · -- Two Phase-1 jobs on one machine: stop at σ1.
    use σ1
    have h_opt1 : OPT σ1 = a5 := opt_of_identical_jobs (m := 5) a5 a5_pos
    have hlb : PseudoLB5 σ1 = a5 := by
      change PseudoLB5 [a5, a5, a5, a5, a5] = a5
      exact s1_pseudoLB
    calc
      (1 + gamma5) * PseudoLB5 σ1 = (1 + gamma5) * a5 := by rw [hlb]
      _ ≤ 2 * a5 := by nlinarith [gamma5_le_one, a5_pos]
      _ = 2 * OPT σ1 := by rw [h_opt1]
      _ ≤ algorithmMakespan 5 alg σ1 := h_imbal1

  · -- Phase 1 balanced: all loads = a5.
    let loads1 : Loads 5 := runAlgorithm 5 alg σ1
    have h_loads1 : ∀ i : Fin 5, loads1 i = a5 := h_bal1
    let σ2 : JobSequence := σ1 ++ List.replicate 5 b5
    have h_layer2 := layer_separation_from_base (m := 5) alg a5 b5 b5_pos loads1 h_loads1
    rcases h_layer2 with h_imbal2 | h_bal2
    · -- Two Phase-2 jobs collide: stop at σ2.
      use σ2
      have hlb : PseudoLB5 σ2 = gamma5 - 1 / 2 := by
        change PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5] = gamma5 - 1 / 2
        exact s2_pseudoLB
      have h_run2 : runAlgorithm 5 alg σ2 =
          (List.replicate 5 b5).foldl (step (m := 5) alg) loads1 := by
        simp [σ2, σ1, runAlgorithm, loads1]
      have h_mk : a5 + 2 * b5 ≤ algorithmMakespan 5 alg σ2 := by
        dsimp [algorithmMakespan]
        rw [h_run2]
        exact h_imbal2
      calc
        (1 + gamma5) * PseudoLB5 σ2 = (1 + gamma5) * (gamma5 - 1 / 2) := by rw [hlb]
        _ = a5 + 2 * b5 := a5_add_two_b5_eq.symm
        _ ≤ algorithmMakespan 5 alg σ2 := h_mk

    · -- Phase 2 balanced: all loads = a5 + b5 = gamma5 - 1/2.
      let loads2 : Loads 5 := runAlgorithm 5 alg σ2
      have h_run2 : loads2 = (List.replicate 5 b5).foldl (step (m := 5) alg) loads1 := by
        simp [loads2, σ2, σ1, runAlgorithm, loads1]
      have h_loads2 : ∀ i : Fin 5, loads2 i = a5 + b5 := by
        simpa [h_run2] using h_bal2
      -- Phase 3: four jobs of size 1/2.
      let m5 : Fin 5 := alg loads2 (1 / 2)
      let loads3 : Loads 5 := step (m := 5) alg loads2 (1 / 2)
      let m6 : Fin 5 := alg loads3 (1 / 2)
      let loads4 : Loads 5 := step (m := 5) alg loads3 (1 / 2)
      let m7 : Fin 5 := alg loads4 (1 / 2)
      let loads5 : Loads 5 := step (m := 5) alg loads4 (1 / 2)
      let m8 : Fin 5 := alg loads5 (1 / 2)
      let loads6 : Loads 5 := step (m := 5) alg loads5 (1 / 2)
      let σ3 : JobSequence := σ2 ++ [1 / 2, 1 / 2, 1 / 2, 1 / 2]
      have h_run3 : runAlgorithm 5 alg σ3 = loads6 := by
        simp [σ3, σ2, σ1, runAlgorithm, loads1, loads2, loads3, loads4, loads5, loads6]
      by_cases h_coll3 :
        m5 = m6 ∨ m5 = m7 ∨ m5 = m8 ∨ m6 = m7 ∨ m6 = m8 ∨ m7 = m8
      · -- Two Phase-3 jobs collide: stop at σ3.
        use σ3
        have hlb : PseudoLB5 σ3 = 161 / 240 := by
          change PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5,
            1 / 2, 1 / 2, 1 / 2, 1 / 2] = 161 / 240
          exact s3_pseudoLB
        have h_mk : gamma5 + 1 / 2 ≤ algorithmMakespan 5 alg σ3 := by
          dsimp [algorithmMakespan]
          rw [h_run3]
          rcases h_coll3 with h56 | h57 | h58 | h67 | h68 | h78
          · -- m5 = m6
            have h3 : loads3 m5 = a5 + b5 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h4_ge : a5 + b5 + 1 ≤ loads4 m5 := by
              have hm6_def : alg loads3 (1 / 2) = m5 := by simpa [m6] using h56.symm
              dsimp [loads4, step]
              rw [hm6_def]
              split_ifs with hif
              · nlinarith [h3]
              · exfalso
                exact hif rfl
            have h6_ge : a5 + b5 + 1 ≤ loads6 m5 := by
              have hle : loads4 m5 ≤ loads6 m5 := by
                dsimp [loads6, loads5, step]
                split_ifs <;> nlinarith [h4_ge]
              nlinarith [h4_ge, hle]
            have h_l : gamma5 + 1 / 2 ≤ loads6 m5 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m5
            nlinarith
          · -- m5 = m7
            have h3 : loads3 m5 = a5 + b5 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h5_ge : a5 + b5 + 1 ≤ loads5 m5 := by
              have hm7_def : alg loads4 (1 / 2) = m5 := by simpa [m7] using h57.symm
              have hle : loads3 m5 ≤ loads4 m5 := by
                dsimp [loads4, step]
                split_ifs <;> nlinarith [h3]
              dsimp [loads5, step]
              rw [hm7_def]
              split_ifs with hif
              · nlinarith [h3, hle]
              · exfalso
                exact hif rfl
            have h6_ge : a5 + b5 + 1 ≤ loads6 m5 := by
              have hle : loads5 m5 ≤ loads6 m5 := by
                dsimp [loads6, step]
                split_ifs <;> nlinarith [h5_ge]
              nlinarith [h5_ge, hle]
            have h_l : gamma5 + 1 / 2 ≤ loads6 m5 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m5
            nlinarith
          · -- m5 = m8
            have h3 : loads3 m5 = a5 + b5 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h6_ge : a5 + b5 + 1 ≤ loads6 m5 := by
              have hm8_def : alg loads5 (1 / 2) = m5 := by simpa [m8] using h58.symm
              have hle : loads3 m5 ≤ loads5 m5 := by
                dsimp [loads5, loads4, step]
                split_ifs <;> nlinarith [h3]
              dsimp [loads6, step]
              rw [hm8_def]
              split_ifs with hif
              · nlinarith [h3, hle]
              · exfalso
                exact hif rfl
            have h_l : gamma5 + 1 / 2 ≤ loads6 m5 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m5
            nlinarith
          · -- m6 = m7
            have h3_ge : a5 + b5 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h5_ge : a5 + b5 + 1 ≤ loads5 m6 := by
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
              nlinarith [h3_ge, h4, h5]
            have h6_ge : a5 + b5 + 1 ≤ loads6 m6 := by
              have hle : loads5 m6 ≤ loads6 m6 := by
                dsimp [loads6, step]
                split_ifs <;> nlinarith [h5_ge]
              nlinarith [h5_ge, hle]
            have h_l : gamma5 + 1 / 2 ≤ loads6 m6 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m6
            nlinarith
          · -- m6 = m8
            have h3_ge : a5 + b5 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h6_ge : a5 + b5 + 1 ≤ loads6 m6 := by
              have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
              have hm8_def : alg loads5 (1 / 2) = m6 := by simpa [m8] using h68.symm
              have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                dsimp [loads4, step]
                rw [hm6_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              have hle5 : loads4 m6 ≤ loads5 m6 := by
                dsimp [loads5, step]
                split_ifs <;> nlinarith [h4]
              dsimp [loads6, step]
              rw [hm8_def]
              split_ifs with hif
              · nlinarith [h3_ge, h4, hle5]
              · exfalso
                exact hif rfl
            have h_l : gamma5 + 1 / 2 ≤ loads6 m6 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m6
            nlinarith
          · -- m7 = m8
            have h3_ge : a5 + b5 ≤ loads3 m7 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m7] <;> norm_num
            have h6_ge : a5 + b5 + 1 ≤ loads6 m7 := by
              have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
              have hm8_def : alg loads5 (1 / 2) = m7 := by simpa [m8] using h78.symm
              have h4_ge : a5 + b5 ≤ loads4 m7 := by
                dsimp [loads4, step]
                split_ifs with hif
                · nlinarith [h3_ge]
                · exact h3_ge
              have h5 : loads5 m7 = loads4 m7 + 1 / 2 := by
                dsimp [loads5, step]
                rw [hm7_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              have h6 : loads6 m7 = loads5 m7 + 1 / 2 := by
                dsimp [loads6, step]
                rw [hm8_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              nlinarith [h4_ge, h5, h6]
            have h_l : gamma5 + 1 / 2 ≤ loads6 m7 := by
              nlinarith [a5_add_b5_eq_gamma, h6_ge]
            have h := makespan_ge_each (m := 5) loads6 m7
            nlinarith
        calc
          (1 + gamma5) * PseudoLB5 σ3 = (1 + gamma5) * (161 / 240) := by rw [hlb]
          _ ≤ gamma5 + 1 / 2 := phase3_bound
          _ ≤ algorithmMakespan 5 alg σ3 := h_mk

      · -- Phase 3 jobs on distinct machines.
        have h56 : m5 ≠ m6 := by intro h; exact h_coll3 (Or.inl h)
        have h57 : m5 ≠ m7 := by intro h; exact h_coll3 (Or.inr (Or.inl h))
        have h58 : m5 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inl h)))
        have h67 : m6 ≠ m7 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have h68 : m6 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        have h78 : m7 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        -- Phase 4: one job of size d5.
        let m9 : Fin 5 := alg loads6 d5
        let loads7 : Loads 5 := step (m := 5) alg loads6 d5
        let σ4 : JobSequence := σ3 ++ [d5]
        have h_run4 : runAlgorithm 5 alg σ4 = loads7 := by
          simp [σ4, σ3, runAlgorithm, loads1, loads2, loads3, loads4, loads5, loads6, loads7]
        by_cases h4 : m9 = m5 ∨ m9 = m6 ∨ m9 = m7 ∨ m9 = m8
        · -- Phase-4 job joins a Phase-3 machine: stop at σ4.
          use σ4
          have hlb : PseudoLB5 σ4 = 4 / 5 := by
            change PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5,
              1 / 2, 1 / 2, 1 / 2, 1 / 2, d5] = 4 / 5
            exact s4_pseudoLB
          have h_mk : gamma5 + d5 ≤ algorithmMakespan 5 alg σ4 := by
            dsimp [algorithmMakespan]
            rw [h_run4]
            have h_loads6_m9 : a5 + b5 + 1 / 2 ≤ loads6 m9 := by
              rcases h4 with h9 | h9 | h9 | h9
              · rw [h9]
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a5 + b5 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have hle : loads3 m5 ≤ loads6 m5 := by
                  dsimp [loads6, loads5, loads4, step]
                  split_ifs <;> nlinarith [h3]
                nlinarith [h3, hle]
              · rw [h9]
                have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                have h3 : loads3 m6 = a5 + b5 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m6 = m5 := by simpa [← hm5_def] using hif
                    exact h56 this.symm
                  · simp [h_loads2 m6]
                have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                  dsimp [loads4, step]
                  rw [hm6_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                have hle : loads4 m6 ≤ loads6 m6 := by
                  dsimp [loads6, loads5, step]
                  split_ifs <;> nlinarith [h4]
                nlinarith [h3, h4, hle]
              · rw [h9]
                have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                have h3 : loads3 m7 = a5 + b5 := by
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
                have h5 : loads5 m7 = loads4 m7 + 1 / 2 := by
                  dsimp [loads5, step]
                  rw [hm7_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                have hle : loads5 m7 ≤ loads6 m7 := by
                  dsimp [loads6, step]
                  split_ifs <;> nlinarith [h5]
                nlinarith [h3, h4, h5, hle]
              · rw [h9]
                have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                have h3 : loads3 m8 = a5 + b5 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m8 = m5 := by simpa [← hm5_def] using hif
                    exact h58 this.symm
                  · simp [h_loads2 m8]
                have h4 : loads4 m8 = loads3 m8 := by
                  dsimp [loads4, step]
                  split_ifs with hif
                  · exfalso
                    have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                    have : m8 = m6 := by simpa [← hm6_def] using hif
                    exact h68 this.symm
                  · rfl
                have h5 : loads5 m8 = loads4 m8 := by
                  dsimp [loads5, step]
                  split_ifs with hif
                  · exfalso
                    have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                    have : m8 = m7 := by simpa [← hm7_def] using hif
                    exact h78 this.symm
                  · rfl
                have h6 : loads6 m8 = loads5 m8 + 1 / 2 := by
                  dsimp [loads6, step]
                  rw [hm8_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                nlinarith [h3, h4, h5, h6]
            have h_loads7_m9 : a5 + b5 + 1 / 2 + d5 ≤ loads7 m9 := by
              have hm9_def : alg loads6 d5 = m9 := by rfl
              dsimp [loads7, step]
              rw [hm9_def]
              split_ifs with hif
              · nlinarith [h_loads6_m9]
              · exfalso
                exact hif rfl
            have h := makespan_ge_each (m := 5) loads7 m9
            nlinarith [a5_add_b5_eq_gamma, h_loads7_m9, h]
          calc
            (1 + gamma5) * PseudoLB5 σ4 = (1 + gamma5) * (4 / 5) := by rw [hlb]
            _ = gamma5 + d5 := gamma5_add_d5_eq.symm
            _ ≤ algorithmMakespan 5 alg σ4 := h_mk

        · -- Phase-4 job joins the untouched machine: all loads ≥ gamma5.
          have h9n : m9 ≠ m5 := by intro h; exact h4 (Or.inl h)
          have h9n6 : m9 ≠ m6 := by intro h; exact h4 (Or.inr (Or.inl h))
          have h9n7 : m9 ≠ m7 := by intro h; exact h4 (Or.inr (Or.inr (Or.inl h)))
          have h9n8 : m9 ≠ m8 := by intro h; exact h4 (Or.inr (Or.inr (Or.inr h)))
          -- Phase 5: one job of size 1.
          let m10 : Fin 5 := alg loads7 (1 : ℝ)
          let loads8 : Loads 5 := step (m := 5) alg loads7 (1 : ℝ)
          let σ5 : JobSequence := σ4 ++ [1]
          use σ5
          have h_run5 : runAlgorithm 5 alg σ5 = loads8 := by
            dsimp [σ5]
            rw [runAlgorithm_append_singleton (m := 5) alg σ4 (1 : ℝ)]
            rw [h_run4]
          have hlb : PseudoLB5 σ5 = 1 := by
            change PseudoLB5 [a5, a5, a5, a5, a5, b5, b5, b5, b5, b5,
              1 / 2, 1 / 2, 1 / 2, 1 / 2, d5, 1] = 1
            exact s5_pseudoLB
          have h_mk : gamma5 + 1 ≤ algorithmMakespan 5 alg σ5 := by
            dsimp [algorithmMakespan]
            rw [h_run5]
            have h_loads8_m10 : loads8 m10 = loads7 m10 + 1 := by
              have hm10_def : alg loads7 (1 : ℝ) = m10 := by rfl
              dsimp [loads8, step]
              rw [hm10_def]
              split_ifs with hif
              · rfl
              · exfalso
                exact hif rfl
            have h_all_ge : ∀ i : Fin 5, gamma5 ≤ loads7 i := by
              intro i
              have hcov : ({m5, m6, m7, m8, m9} : Finset (Fin 5)) = Finset.univ := by
                apply Finset.eq_of_subset_of_card_le
                · exact Finset.subset_univ _
                · rw [Finset.card_univ, Fintype.card_fin]
                  have hcard : ({m5, m6, m7, m8, m9} : Finset (Fin 5)).card = 5 := by
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h | h
                      · exact h56 h
                      · exact h57 h
                      · exact h58 h
                      · exact h9n h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h
                      · exact h67 h
                      · exact h68 h
                      · exact h9n6 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h
                      · exact h78 h
                      · exact h9n7 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      exact h9n8 h.symm)]
                    simp
                  rw [hcard]
              have hmem : i ∈ ({m5, m6, m7, m8, m9} : Finset (Fin 5)) := by
                rw [hcov]
                exact Finset.mem_univ i
              simp at hmem
              rcases hmem with rfl | rfl | rfl | rfl | rfl
              · -- i = m5
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a5 + b5 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have h7 : gamma5 ≤ loads7 m5 := by
                  have hle : loads3 m5 ≤ loads7 m5 := by
                    dsimp [loads7, loads6, loads5, loads4, step]
                    split_ifs <;> nlinarith [h3, d5_pos]
                  nlinarith [a5_add_b5_eq_gamma, h3, hle]
                exact h7
              · -- i = m6
                have h3 : loads3 m6 = a5 + b5 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m6 = m5 := by simpa [← hm5_def] using hif
                    exact h56 this.symm
                  · simp [h_loads2 m6]
                have h7 : gamma5 ≤ loads7 m6 := by
                  have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                  have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                    dsimp [loads4, step]
                    rw [hm6_def]
                    split_ifs with hif
                    · rfl
                    · exfalso
                      exact hif rfl
                  have hle : loads4 m6 ≤ loads7 m6 := by
                    dsimp [loads7, loads6, loads5, step]
                    split_ifs <;> nlinarith [h4, d5_pos]
                  nlinarith [a5_add_b5_eq_gamma, h3, h4, hle]
                exact h7
              · -- i = m7
                have h3 : loads3 m7 = a5 + b5 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m7 = m5 := by simpa [← hm5_def] using hif
                    exact h57 this.symm
                  · simp [h_loads2 m7]
                have h7 : gamma5 ≤ loads7 m7 := by
                  have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                  have h4 : loads4 m7 = loads3 m7 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m7 = m6 := by simpa [← hm6_def] using hif
                      exact h67 this.symm
                    · rfl
                  have h5 : loads5 m7 = loads4 m7 + 1 / 2 := by
                    dsimp [loads5, step]
                    rw [hm7_def]
                    split_ifs with hif
                    · rfl
                    · exfalso
                      exact hif rfl
                  have hle : loads5 m7 ≤ loads7 m7 := by
                    dsimp [loads7, loads6, step]
                    split_ifs <;> nlinarith [h5, d5_pos]
                  nlinarith [a5_add_b5_eq_gamma, h3, h4, h5, hle]
                exact h7
              · -- i = m8
                have h3 : loads3 m8 = a5 + b5 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m8 = m5 := by simpa [← hm5_def] using hif
                    exact h58 this.symm
                  · simp [h_loads2 m8]
                have h7 : gamma5 ≤ loads7 m8 := by
                  have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                  have h4 : loads4 m8 = loads3 m8 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m8 = m6 := by simpa [← hm6_def] using hif
                      exact h68 this.symm
                    · rfl
                  have h5 : loads5 m8 = loads4 m8 := by
                    dsimp [loads5, step]
                    split_ifs with hif
                    · exfalso
                      have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                      have : m8 = m7 := by simpa [← hm7_def] using hif
                      exact h78 this.symm
                    · rfl
                  have h6 : loads6 m8 = loads5 m8 + 1 / 2 := by
                    dsimp [loads6, step]
                    rw [hm8_def]
                    split_ifs with hif
                    · rfl
                    · exfalso
                      exact hif rfl
                  have hle : loads6 m8 ≤ loads7 m8 := by
                    dsimp [loads7, step]
                    split_ifs <;> nlinarith [h6, d5_pos]
                  nlinarith [a5_add_b5_eq_gamma, h3, h4, h5, h6, hle]
                exact h7
              · -- i = m9: load = gamma5 - 1/2 + d5 ≥ gamma5
                have hm9_def : alg loads6 d5 = m9 := by rfl
                have h6 : loads6 m9 = a5 + b5 := by
                  have h3 : loads3 m9 = a5 + b5 := by
                    dsimp [loads3, step]
                    split_ifs with hif
                    · exfalso
                      have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                      have : m9 = m5 := by simpa [← hm5_def] using hif
                      exact h9n this
                    · simp [h_loads2 m9]
                  have h4 : loads4 m9 = loads3 m9 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m9 = m6 := by simpa [← hm6_def] using hif
                      exact h9n6 this
                    · rfl
                  have h5 : loads5 m9 = loads4 m9 := by
                    dsimp [loads5, step]
                    split_ifs with hif
                    · exfalso
                      have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                      have : m9 = m7 := by simpa [← hm7_def] using hif
                      exact h9n7 this
                    · rfl
                  have h6 : loads6 m9 = loads5 m9 := by
                    dsimp [loads6, step]
                    split_ifs with hif
                    · exfalso
                      have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                      have : m9 = m8 := by simpa [← hm8_def] using hif
                      exact h9n8 this
                    · rfl
                  nlinarith [h3, h4, h5, h6]
                have h7 : gamma5 ≤ loads7 m9 := by
                  dsimp [loads7, step]
                  rw [hm9_def]
                  split_ifs with hif
                  · nlinarith [a5_add_b5_eq_gamma, h6, d5_eq]
                  · exfalso
                    exact hif rfl
                exact h7
            have h := makespan_ge_each (m := 5) loads8 m10
            rw [h_loads8_m10] at h
            nlinarith [h_all_ge m10, h]
          calc
            (1 + gamma5) * PseudoLB5 σ5 = (1 + gamma5) * 1 := by rw [hlb]
            _ = gamma5 + 1 := gamma5_add_one_eq.symm
            _ ≤ algorithmMakespan 5 alg σ5 := h_mk

end OnlineScheduling
