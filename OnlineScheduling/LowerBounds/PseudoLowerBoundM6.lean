/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Pseudo Lower Bounds (Tan & Li, 2015), m = 6

For 6 machines, using only the weak lower bounds
`LB1 = totalLoad / m` and `LB2 = maxJobSize` on the optimum makespan,
no online algorithm can be proved to have competitive ratio below
`1 + gamma6 = 1 + 4/5`.

Adaptive adversary (`gamma = 4/5`, `q = 1`):
  Phase 1: 6 jobs of `a = (1-gamma)(gamma-1/2) = 3/50`
  Phase 2: 6 jobs of `b = gamma(gamma-1/2) = 6/25`
  Phase 3: 5 jobs of `1/2`
  Phase 4: 1 job of `d = (5-gamma)/6 = 7/10`
  Phase 5: 1 job of `1`
Stop at the first phase where two jobs collide; otherwise keep going.
In every stopping prefix `sigma`, the makespan is at least
`(1+gamma) * max (totalLoad sigma / 6) (maxJobSize sigma)`.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

set_option maxHeartbeats 4000000

open Finset

namespace OnlineScheduling

noncomputable def gamma6 : ℝ := 4 / 5
noncomputable def a6 : ℝ := (1 - gamma6) * (gamma6 - 1 / 2)
noncomputable def b6 : ℝ := gamma6 * (gamma6 - 1 / 2)
noncomputable def d6 : ℝ := (5 - gamma6) / 6

private lemma a6_eq : a6 = 3 / 50 := by norm_num [a6, gamma6]
private lemma b6_eq : b6 = 6 / 25 := by norm_num [b6, gamma6]
private lemma d6_eq : d6 = 7 / 10 := by norm_num [d6, gamma6]
private lemma gamma6_pos : 0 < gamma6 := by norm_num [gamma6]
private lemma a6_pos : 0 < a6 := by norm_num [a6, gamma6]
private lemma b6_pos : 0 < b6 := by norm_num [b6, gamma6]
private lemma d6_pos : 0 < d6 := by norm_num [d6, gamma6]

/-- The weak pseudo lower bound: `max` of average load and largest job. -/
noncomputable def PseudoLB6 (sigma : JobSequence) : ℝ :=
  max (totalLoad sigma / 6) (maxJobSize sigma)

private lemma gamma6_le_one : gamma6 ≤ 1 := by norm_num [gamma6]

/-- `a6 + 2*b6 = (1+gamma6)(gamma6 - 1/2)`, the Phase-2 collision bound. -/
private lemma a6_add_two_b6_eq : a6 + 2 * b6 = (1 + gamma6) * (gamma6 - 1 / 2) := by
  rw [a6_eq, b6_eq]
  norm_num [gamma6]

/-- `gamma6 + d6 = (1+gamma6) * (5/6)`, the Phase-4 collision bound. -/
private lemma gamma6_add_d6_eq : gamma6 + d6 = (1 + gamma6) * (5 / 6) := by
  rw [d6_eq]
  norm_num [gamma6]

/-- `gamma6 + 1 = (1+gamma6) * 1`, the Phase-5 bound. -/
private lemma gamma6_add_one_eq : gamma6 + 1 = (1 + gamma6) * 1 := by ring

/-- Phase-3 collision makespan `gamma6 + 1/2` dominates `(1+gamma6)*43/60`. -/
private lemma phase3_bound6 : (1 + gamma6) * (43 / 60) ≤ gamma6 + 1 / 2 := by
  norm_num [gamma6]

/-- `a6 + b6 = gamma6 - 1/2`, the balanced load after Phases 1 and 2. -/
private lemma a6_add_b6_eq_gamma : a6 + b6 = gamma6 - 1 / 2 := by
  rw [a6_eq, b6_eq]
  norm_num [gamma6]

private lemma s1_pseudoLB6 : PseudoLB6 [a6, a6, a6, a6, a6, a6] = a6 := by
  dsimp [PseudoLB6, totalLoad, maxJobSize]
  rw [a6_eq]
  norm_num

private lemma s2_pseudoLB6 :
    PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6] = gamma6 - 1 / 2 := by
  dsimp [PseudoLB6, totalLoad, maxJobSize]
  rw [a6_eq, b6_eq]
  norm_num [gamma6]

private lemma s3_pseudoLB6 :
    PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
      1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2] = 43 / 60 := by
  dsimp [PseudoLB6, totalLoad, maxJobSize]
  rw [a6_eq, b6_eq]
  norm_num [gamma6]

private lemma s4_pseudoLB6 :
    PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
      1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d6] = 5 / 6 := by
  dsimp [PseudoLB6, totalLoad, maxJobSize]
  rw [a6_eq, b6_eq, d6_eq]
  norm_num [gamma6]

private lemma s5_pseudoLB6 :
    PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
      1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d6, 1] = 1 := by
  dsimp [PseudoLB6, totalLoad, maxJobSize]
  rw [a6_eq, b6_eq, d6_eq]
  norm_num [gamma6]

/-- For 6 machines, using only the weak lower bounds on the optimum makespan,
    no online algorithm can be proved to have competitive ratio below `1 + 4/5`. -/
theorem m6_pseudo_lower_bound (alg : OnlineAlgorithm 6) :
    ∃ sigma : JobSequence, algorithmMakespan 6 alg sigma ≥ (1 + gamma6) * PseudoLB6 sigma := by
  let σ1 : JobSequence := List.replicate 6 a6
  have h_layer1 := layer_separation (m := 6) alg a6 a6_pos
  rcases h_layer1 with h_imbal1 | h_bal1
  · -- Two Phase-1 jobs on one machine: stop at σ1.
    use σ1
    have h_opt1 : OPT σ1 = a6 := opt_of_identical_jobs (m := 6) a6 a6_pos
    have hlb : PseudoLB6 σ1 = a6 := by
      change PseudoLB6 [a6, a6, a6, a6, a6, a6] = a6
      exact s1_pseudoLB6
    calc
      (1 + gamma6) * PseudoLB6 σ1 = (1 + gamma6) * a6 := by rw [hlb]
      _ ≤ 2 * a6 := by nlinarith [gamma6_le_one, a6_pos]
      _ = 2 * OPT σ1 := by rw [h_opt1]
      _ ≤ algorithmMakespan 6 alg σ1 := h_imbal1

  · -- Phase 1 balanced: all loads = a6.
    let loads1 : Loads 6 := runAlgorithm 6 alg σ1
    have h_loads1 : ∀ i : Fin 6, loads1 i = a6 := h_bal1
    let σ2 : JobSequence := σ1 ++ List.replicate 6 b6
    have h_layer2 := layer_separation_from_base (m := 6) alg a6 b6 b6_pos loads1 h_loads1
    rcases h_layer2 with h_imbal2 | h_bal2
    · -- Two Phase-2 jobs collide: stop at σ2.
      use σ2
      have hlb : PseudoLB6 σ2 = gamma6 - 1 / 2 := by
        change PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6] = gamma6 - 1 / 2
        exact s2_pseudoLB6
      have h_run2 : runAlgorithm 6 alg σ2 =
          (List.replicate 6 b6).foldl (step (m := 6) alg) loads1 := by
        simp [σ2, σ1, runAlgorithm, loads1]
      have h_mk : a6 + 2 * b6 ≤ algorithmMakespan 6 alg σ2 := by
        dsimp [algorithmMakespan]
        rw [h_run2]
        exact h_imbal2
      calc
        (1 + gamma6) * PseudoLB6 σ2 = (1 + gamma6) * (gamma6 - 1 / 2) := by rw [hlb]
        _ = a6 + 2 * b6 := a6_add_two_b6_eq.symm
        _ ≤ algorithmMakespan 6 alg σ2 := h_mk

    · -- Phase 2 balanced: all loads = a6 + b6 = gamma6 - 1/2.
      let loads2 : Loads 6 := runAlgorithm 6 alg σ2
      have h_run2 : loads2 = (List.replicate 6 b6).foldl (step (m := 6) alg) loads1 := by
        simp [loads2, σ2, σ1, runAlgorithm, loads1]
      have h_loads2 : ∀ i : Fin 6, loads2 i = a6 + b6 := by
        simpa [h_run2] using h_bal2
      -- Phase 3: five jobs of size 1/2.
      let m5 : Fin 6 := alg loads2 (1 / 2)
      let loads3 : Loads 6 := step (m := 6) alg loads2 (1 / 2)
      let m6 : Fin 6 := alg loads3 (1 / 2)
      let loads4 : Loads 6 := step (m := 6) alg loads3 (1 / 2)
      let m7 : Fin 6 := alg loads4 (1 / 2)
      let loads5 : Loads 6 := step (m := 6) alg loads4 (1 / 2)
      let m8 : Fin 6 := alg loads5 (1 / 2)
      let loads6 : Loads 6 := step (m := 6) alg loads5 (1 / 2)
      let m9 : Fin 6 := alg loads6 (1 / 2)
      let loads7 : Loads 6 := step (m := 6) alg loads6 (1 / 2)
      let σ3 : JobSequence := σ2 ++ [1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2]
      have h_run3 : runAlgorithm 6 alg σ3 = loads7 := by
        simp [σ3, σ2, σ1, runAlgorithm, loads2, loads3, loads4, loads5, loads6, loads7]
      by_cases h_coll3 :
        m5 = m6 ∨ m5 = m7 ∨ m5 = m8 ∨ m5 = m9 ∨ m6 = m7 ∨ m6 = m8 ∨ m6 = m9 ∨
          m7 = m8 ∨ m7 = m9 ∨ m8 = m9
      · -- Two Phase-3 jobs collide: stop at σ3.
        use σ3
        have hlb : PseudoLB6 σ3 = 43 / 60 := by
          change PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
            1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2] = 43 / 60
          exact s3_pseudoLB6
        have h_mk : gamma6 + 1 / 2 ≤ algorithmMakespan 6 alg σ3 := by
          dsimp [algorithmMakespan]
          rw [h_run3]
          rcases h_coll3 with h56 | h57 | h58 | h59 | h67 | h68 | h69 | h78 | h79 | h89
          · -- m5 = m6
            have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h4_ge : a6 + b6 + 1 ≤ loads4 m5 := by
              have hm6_def : alg loads3 (1 / 2) = m5 := by simpa [m6] using h56.symm
              dsimp [loads4, step]
              rw [hm6_def]
              split_ifs with hif
              · nlinarith [h3]
              · exfalso
                exact hif rfl
            have h7_ge : a6 + b6 + 1 ≤ loads7 m5 := by
              have hle : loads4 m5 ≤ loads7 m5 := by
                dsimp [loads7, loads6, loads5, step]
                split_ifs <;> nlinarith [h4_ge]
              nlinarith [h4_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m5 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m5
            nlinarith
          · -- m5 = m7
            have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h5_ge : a6 + b6 + 1 ≤ loads5 m5 := by
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
            have h7_ge : a6 + b6 + 1 ≤ loads7 m5 := by
              have hle : loads5 m5 ≤ loads7 m5 := by
                dsimp [loads7, loads6, step]
                split_ifs <;> nlinarith [h5_ge]
              nlinarith [h5_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m5 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m5
            nlinarith
          · -- m5 = m8
            have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h6_ge : a6 + b6 + 1 ≤ loads6 m5 := by
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
            have h7_ge : a6 + b6 + 1 ≤ loads7 m5 := by
              have hle : loads6 m5 ≤ loads7 m5 := by
                dsimp [loads7, step]
                split_ifs <;> nlinarith [h6_ge]
              nlinarith [h6_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m5 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m5
            nlinarith
          · -- m5 = m9
            have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
              have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
              dsimp [loads3, step]
              rw [hm5_def]
              simp [h_loads2 m5]
            have h7_ge : a6 + b6 + 1 ≤ loads7 m5 := by
              have hm9_def : alg loads6 (1 / 2) = m5 := by simpa [m9] using h59.symm
              have hle : loads3 m5 ≤ loads6 m5 := by
                dsimp [loads6, loads5, loads4, step]
                split_ifs <;> nlinarith [h3]
              dsimp [loads7, step]
              rw [hm9_def]
              split_ifs with hif
              · nlinarith [h3, hle]
              · exfalso
                exact hif rfl
            have h_l : gamma6 + 1 / 2 ≤ loads7 m5 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m5
            nlinarith
          · -- m6 = m7
            have h3_ge : a6 + b6 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h5_ge : a6 + b6 + 1 ≤ loads5 m6 := by
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
            have h7_ge : a6 + b6 + 1 ≤ loads7 m6 := by
              have hle : loads5 m6 ≤ loads7 m6 := by
                dsimp [loads7, loads6, step]
                split_ifs <;> nlinarith [h5_ge]
              nlinarith [h5_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m6 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m6
            nlinarith
          · -- m6 = m8
            have h3_ge : a6 + b6 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h6_ge : a6 + b6 + 1 ≤ loads6 m6 := by
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
            have h7_ge : a6 + b6 + 1 ≤ loads7 m6 := by
              have hle : loads6 m6 ≤ loads7 m6 := by
                dsimp [loads7, step]
                split_ifs <;> nlinarith [h6_ge]
              nlinarith [h6_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m6 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m6
            nlinarith
          · -- m6 = m9
            have h3_ge : a6 + b6 ≤ loads3 m6 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m6] <;> norm_num
            have h7_ge : a6 + b6 + 1 ≤ loads7 m6 := by
              have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
              have hm9_def : alg loads6 (1 / 2) = m6 := by simpa [m9] using h69.symm
              have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                dsimp [loads4, step]
                rw [hm6_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              have hle6 : loads4 m6 ≤ loads6 m6 := by
                dsimp [loads6, loads5, step]
                split_ifs <;> nlinarith [h4]
              dsimp [loads7, step]
              rw [hm9_def]
              split_ifs with hif
              · nlinarith [h3_ge, h4, hle6]
              · exfalso
                exact hif rfl
            have h_l : gamma6 + 1 / 2 ≤ loads7 m6 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m6
            nlinarith
          · -- m7 = m8
            have h3_ge : a6 + b6 ≤ loads3 m7 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m7] <;> norm_num
            have h6_ge : a6 + b6 + 1 ≤ loads6 m7 := by
              have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
              have hm8_def : alg loads5 (1 / 2) = m7 := by simpa [m8] using h78.symm
              have h4_ge : a6 + b6 ≤ loads4 m7 := by
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
            have h7_ge : a6 + b6 + 1 ≤ loads7 m7 := by
              have hle : loads6 m7 ≤ loads7 m7 := by
                dsimp [loads7, step]
                split_ifs <;> nlinarith [h6_ge]
              nlinarith [h6_ge, hle]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m7 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m7
            nlinarith
          · -- m7 = m9
            have h3_ge : a6 + b6 ≤ loads3 m7 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m7] <;> norm_num
            have h7_ge : a6 + b6 + 1 ≤ loads7 m7 := by
              have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
              have hm9_def : alg loads6 (1 / 2) = m7 := by simpa [m9] using h79.symm
              have h4_ge : a6 + b6 ≤ loads4 m7 := by
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
              have hle6 : loads5 m7 ≤ loads6 m7 := by
                dsimp [loads6, step]
                split_ifs <;> nlinarith [h5]
              dsimp [loads7, step]
              rw [hm9_def]
              split_ifs with hif
              · nlinarith [h4_ge, h5, hle6]
              · exfalso
                exact hif rfl
            have h_l : gamma6 + 1 / 2 ≤ loads7 m7 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m7
            nlinarith
          · -- m8 = m9
            have h3_ge : a6 + b6 ≤ loads3 m8 := by
              dsimp [loads3, step]
              split_ifs <;> simp [h_loads2 m8] <;> norm_num
            have h7_ge : a6 + b6 + 1 ≤ loads7 m8 := by
              have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
              have hm9_def : alg loads6 (1 / 2) = m8 := by simpa [m9] using h89.symm
              have hle5 : loads3 m8 ≤ loads5 m8 := by
                dsimp [loads5, loads4, step]
                split_ifs <;> nlinarith [h3_ge]
              have h6 : loads6 m8 = loads5 m8 + 1 / 2 := by
                dsimp [loads6, step]
                rw [hm8_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              have h7 : loads7 m8 = loads6 m8 + 1 / 2 := by
                dsimp [loads7, step]
                rw [hm9_def]
                split_ifs with hif
                · rfl
                · exfalso
                  exact hif rfl
              nlinarith [h3_ge, hle5, h6, h7]
            have h_l : gamma6 + 1 / 2 ≤ loads7 m8 := by
              nlinarith [a6_add_b6_eq_gamma, h7_ge]
            have h := makespan_ge_each (m := 6) loads7 m8
            nlinarith
        calc
          (1 + gamma6) * PseudoLB6 σ3 = (1 + gamma6) * (43 / 60) := by rw [hlb]
          _ ≤ gamma6 + 1 / 2 := phase3_bound6
          _ ≤ algorithmMakespan 6 alg σ3 := h_mk

      · -- Phase 3 jobs on distinct machines.
        have h56 : m5 ≠ m6 := by intro h; exact h_coll3 (Or.inl h)
        have h57 : m5 ≠ m7 := by intro h; exact h_coll3 (Or.inr (Or.inl h))
        have h58 : m5 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inl h)))
        have h59 : m5 ≠ m9 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have h67 : m6 ≠ m7 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        have h68 : m6 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        have h69 : m6 ≠ m9 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
        have h78 : m7 ≠ m8 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
        have h79 : m7 ≠ m9 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
        have h89 : m8 ≠ m9 := by intro h; exact h_coll3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))
        -- Phase 4: one job of size d6.
        let m10 : Fin 6 := alg loads7 d6
        let loads8 : Loads 6 := step (m := 6) alg loads7 d6
        let σ4 : JobSequence := σ3 ++ [d6]
        have h_run4 : runAlgorithm 6 alg σ4 = loads8 := by
          simp [σ4, σ3, runAlgorithm, loads2, loads3, loads4, loads5, loads6, loads7, loads8]
        by_cases h4 : m10 = m5 ∨ m10 = m6 ∨ m10 = m7 ∨ m10 = m8 ∨ m10 = m9
        · -- Phase-4 job joins a Phase-3 machine: stop at σ4.
          use σ4
          have hlb : PseudoLB6 σ4 = 5 / 6 := by
            change PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
              1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d6] = 5 / 6
            exact s4_pseudoLB6
          have h_mk : gamma6 + d6 ≤ algorithmMakespan 6 alg σ4 := by
            dsimp [algorithmMakespan]
            rw [h_run4]
            have h_loads7_m10 : a6 + b6 + 1 / 2 ≤ loads7 m10 := by
              rcases h4 with h10 | h10 | h10 | h10 | h10
              · rw [h10]
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have hle : loads3 m5 ≤ loads7 m5 := by
                  dsimp [loads7, loads6, loads5, loads4, step]
                  split_ifs <;> nlinarith [h3]
                nlinarith [h3, hle]
              · rw [h10]
                have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                have h3 : loads3 m6 = a6 + b6 := by
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
                have hle : loads4 m6 ≤ loads7 m6 := by
                  dsimp [loads7, loads6, loads5, step]
                  split_ifs <;> nlinarith [h4]
                nlinarith [h3, h4, hle]
              · rw [h10]
                have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                have h3 : loads3 m7 = a6 + b6 := by
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
                have hle : loads5 m7 ≤ loads7 m7 := by
                  dsimp [loads7, loads6, step]
                  split_ifs <;> nlinarith [h5]
                nlinarith [h3, h4, h5, hle]
              · rw [h10]
                have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                have h3 : loads3 m8 = a6 + b6 := by
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
                have hle : loads6 m8 ≤ loads7 m8 := by
                  dsimp [loads7, step]
                  split_ifs <;> nlinarith [h6]
                nlinarith [h3, h4, h5, h6, hle]
              · rw [h10]
                have hm9_def : alg loads6 (1 / 2) = m9 := by rfl
                have h3 : loads3 m9 = a6 + b6 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m9 = m5 := by simpa [← hm5_def] using hif
                    exact h59 this.symm
                  · simp [h_loads2 m9]
                have h4 : loads4 m9 = loads3 m9 := by
                  dsimp [loads4, step]
                  split_ifs with hif
                  · exfalso
                    have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                    have : m9 = m6 := by simpa [← hm6_def] using hif
                    exact h69 this.symm
                  · rfl
                have h5 : loads5 m9 = loads4 m9 := by
                  dsimp [loads5, step]
                  split_ifs with hif
                  · exfalso
                    have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                    have : m9 = m7 := by simpa [← hm7_def] using hif
                    exact h79 this.symm
                  · rfl
                have h6 : loads6 m9 = loads5 m9 := by
                  dsimp [loads6, step]
                  split_ifs with hif
                  · exfalso
                    have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                    have : m9 = m8 := by simpa [← hm8_def] using hif
                    exact h89 this.symm
                  · rfl
                have h7 : loads7 m9 = loads6 m9 + 1 / 2 := by
                  dsimp [loads7, step]
                  rw [hm9_def]
                  split_ifs with hif
                  · rfl
                  · exfalso
                    exact hif rfl
                nlinarith [h3, h4, h5, h6, h7]
            have h_loads8_m10 : a6 + b6 + 1 / 2 + d6 ≤ loads8 m10 := by
              have hm10_def : alg loads7 d6 = m10 := by rfl
              dsimp [loads8, step]
              rw [hm10_def]
              split_ifs with hif
              · nlinarith [h_loads7_m10]
              · exfalso
                exact hif rfl
            have h := makespan_ge_each (m := 6) loads8 m10
            nlinarith [a6_add_b6_eq_gamma, h_loads8_m10, h]
          calc
            (1 + gamma6) * PseudoLB6 σ4 = (1 + gamma6) * (5 / 6) := by rw [hlb]
            _ = gamma6 + d6 := gamma6_add_d6_eq.symm
            _ ≤ algorithmMakespan 6 alg σ4 := h_mk

        · -- Phase-4 job joins the untouched machine: all loads ≥ gamma6.
          have h10n : m10 ≠ m5 := by intro h; exact h4 (Or.inl h)
          have h10n6 : m10 ≠ m6 := by intro h; exact h4 (Or.inr (Or.inl h))
          have h10n7 : m10 ≠ m7 := by intro h; exact h4 (Or.inr (Or.inr (Or.inl h)))
          have h10n8 : m10 ≠ m8 := by intro h; exact h4 (Or.inr (Or.inr (Or.inr (Or.inl h))))
          have h10n9 : m10 ≠ m9 := by intro h; exact h4 (Or.inr (Or.inr (Or.inr (Or.inr h))))
          -- Phase 5: one job of size 1.
          let m11 : Fin 6 := alg loads8 (1 : ℝ)
          let loads9 : Loads 6 := step (m := 6) alg loads8 (1 : ℝ)
          let σ5 : JobSequence := σ4 ++ [1]
          use σ5
          have h_run5 : runAlgorithm 6 alg σ5 = loads9 := by
            dsimp [σ5]
            rw [runAlgorithm_append_singleton (m := 6) alg σ4 (1 : ℝ)]
            rw [h_run4]
          have hlb : PseudoLB6 σ5 = 1 := by
            change PseudoLB6 [a6, a6, a6, a6, a6, a6, b6, b6, b6, b6, b6, b6,
              1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, d6, 1] = 1
            exact s5_pseudoLB6
          have h_mk : gamma6 + 1 ≤ algorithmMakespan 6 alg σ5 := by
            dsimp [algorithmMakespan]
            rw [h_run5]
            have h_loads9_m11 : loads9 m11 = loads8 m11 + 1 := by
              have hm11_def : alg loads8 (1 : ℝ) = m11 := by rfl
              dsimp [loads9, step]
              rw [hm11_def]
              split_ifs with hif
              · rfl
              · exfalso
                exact hif rfl
            have h_all_ge : ∀ i : Fin 6, gamma6 ≤ loads8 i := by
              intro i
              have hcov : ({m5, m6, m7, m8, m9, m10} : Finset (Fin 6)) = Finset.univ := by
                apply Finset.eq_of_subset_of_card_le
                · exact Finset.subset_univ _
                · rw [Finset.card_univ, Fintype.card_fin]
                  have hcard : ({m5, m6, m7, m8, m9, m10} : Finset (Fin 6)).card = 6 := by
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h | h | h
                      · exact h56 h
                      · exact h57 h
                      · exact h58 h
                      · exact h59 h
                      · exact h10n h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h | h
                      · exact h67 h
                      · exact h68 h
                      · exact h69 h
                      · exact h10n6 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h | h
                      · exact h78 h
                      · exact h79 h
                      · exact h10n7 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      rcases h with h | h
                      · exact h89 h
                      · exact h10n8 h.symm)]
                    rw [Finset.card_insert_of_notMem (by
                      intro h
                      simp at h
                      exact h10n9 h.symm)]
                    simp
                  rw [hcard]
              have hmem : i ∈ ({m5, m6, m7, m8, m9, m10} : Finset (Fin 6)) := by
                rw [hcov]
                exact Finset.mem_univ i
              simp at hmem
              rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
              · -- i = m5
                have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                have h3 : loads3 m5 = a6 + b6 + 1 / 2 := by
                  dsimp [loads3, step]
                  rw [hm5_def]
                  simp [h_loads2 m5]
                have h8 : gamma6 ≤ loads8 m5 := by
                  have hle : loads3 m5 ≤ loads8 m5 := by
                    dsimp [loads8, loads7, loads6, loads5, loads4, step]
                    split_ifs <;> nlinarith [h3, d6_pos]
                  nlinarith [a6_add_b6_eq_gamma, h3, hle]
                exact h8
              · -- i = m6
                have h3 : loads3 m6 = a6 + b6 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m6 = m5 := by simpa [← hm5_def] using hif
                    exact h56 this.symm
                  · simp [h_loads2 m6]
                have h8 : gamma6 ≤ loads8 m6 := by
                  have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                  have h4 : loads4 m6 = loads3 m6 + 1 / 2 := by
                    dsimp [loads4, step]
                    rw [hm6_def]
                    split_ifs with hif
                    · rfl
                    · exfalso
                      exact hif rfl
                  have hle : loads4 m6 ≤ loads8 m6 := by
                    dsimp [loads8, loads7, loads6, loads5, step]
                    split_ifs <;> nlinarith [h4, d6_pos]
                  nlinarith [a6_add_b6_eq_gamma, h3, h4, hle]
                exact h8
              · -- i = m7
                have h3 : loads3 m7 = a6 + b6 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m7 = m5 := by simpa [← hm5_def] using hif
                    exact h57 this.symm
                  · simp [h_loads2 m7]
                have h8 : gamma6 ≤ loads8 m7 := by
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
                  have hle : loads5 m7 ≤ loads8 m7 := by
                    dsimp [loads8, loads7, loads6, step]
                    split_ifs <;> nlinarith [h5, d6_pos]
                  nlinarith [a6_add_b6_eq_gamma, h3, h4, h5, hle]
                exact h8
              · -- i = m8
                have h3 : loads3 m8 = a6 + b6 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m8 = m5 := by simpa [← hm5_def] using hif
                    exact h58 this.symm
                  · simp [h_loads2 m8]
                have h8 : gamma6 ≤ loads8 m8 := by
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
                  have hle : loads6 m8 ≤ loads8 m8 := by
                    dsimp [loads8, loads7, step]
                    split_ifs <;> nlinarith [h6, d6_pos]
                  nlinarith [a6_add_b6_eq_gamma, h3, h4, h5, h6, hle]
                exact h8
              · -- i = m9
                have h3 : loads3 m9 = a6 + b6 := by
                  dsimp [loads3, step]
                  split_ifs with hif
                  · exfalso
                    have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                    have : m9 = m5 := by simpa [← hm5_def] using hif
                    exact h59 this.symm
                  · simp [h_loads2 m9]
                have h8 : gamma6 ≤ loads8 m9 := by
                  have hm9_def : alg loads6 (1 / 2) = m9 := by rfl
                  have h4 : loads4 m9 = loads3 m9 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m9 = m6 := by simpa [← hm6_def] using hif
                      exact h69 this.symm
                    · rfl
                  have h5 : loads5 m9 = loads4 m9 := by
                    dsimp [loads5, step]
                    split_ifs with hif
                    · exfalso
                      have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                      have : m9 = m7 := by simpa [← hm7_def] using hif
                      exact h79 this.symm
                    · rfl
                  have h6 : loads6 m9 = loads5 m9 := by
                    dsimp [loads6, step]
                    split_ifs with hif
                    · exfalso
                      have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                      have : m9 = m8 := by simpa [← hm8_def] using hif
                      exact h89 this.symm
                    · rfl
                  have h7 : loads7 m9 = loads6 m9 + 1 / 2 := by
                    dsimp [loads7, step]
                    rw [hm9_def]
                    split_ifs with hif
                    · rfl
                    · exfalso
                      exact hif rfl
                  have hle : loads7 m9 ≤ loads8 m9 := by
                    dsimp [loads8, step]
                    split_ifs <;> nlinarith [h7, d6_pos]
                  nlinarith [a6_add_b6_eq_gamma, h3, h4, h5, h6, h7, hle]
                exact h8
              · -- i = m10: load = gamma6 - 1/2 + d6 ≥ gamma6
                have hm10_def : alg loads7 d6 = m10 := by rfl
                have h7eq : loads7 m10 = a6 + b6 := by
                  have h3 : loads3 m10 = a6 + b6 := by
                    dsimp [loads3, step]
                    split_ifs with hif
                    · exfalso
                      have hm5_def : alg loads2 (1 / 2) = m5 := by rfl
                      have : m10 = m5 := by simpa [← hm5_def] using hif
                      exact h10n this
                    · simp [h_loads2 m10]
                  have h4 : loads4 m10 = loads3 m10 := by
                    dsimp [loads4, step]
                    split_ifs with hif
                    · exfalso
                      have hm6_def : alg loads3 (1 / 2) = m6 := by rfl
                      have : m10 = m6 := by simpa [← hm6_def] using hif
                      exact h10n6 this
                    · rfl
                  have h5 : loads5 m10 = loads4 m10 := by
                    dsimp [loads5, step]
                    split_ifs with hif
                    · exfalso
                      have hm7_def : alg loads4 (1 / 2) = m7 := by rfl
                      have : m10 = m7 := by simpa [← hm7_def] using hif
                      exact h10n7 this
                    · rfl
                  have h6 : loads6 m10 = loads5 m10 := by
                    dsimp [loads6, step]
                    split_ifs with hif
                    · exfalso
                      have hm8_def : alg loads5 (1 / 2) = m8 := by rfl
                      have : m10 = m8 := by simpa [← hm8_def] using hif
                      exact h10n8 this
                    · rfl
                  have h7 : loads7 m10 = loads6 m10 := by
                    dsimp [loads7, step]
                    split_ifs with hif
                    · exfalso
                      have hm9_def : alg loads6 (1 / 2) = m9 := by rfl
                      have : m10 = m9 := by simpa [← hm9_def] using hif
                      exact h10n9 this
                    · rfl
                  nlinarith [h3, h4, h5, h6, h7]
                have h8 : gamma6 ≤ loads8 m10 := by
                  dsimp [loads8, step]
                  rw [hm10_def]
                  split_ifs with hif
                  · nlinarith [a6_add_b6_eq_gamma, h7eq, d6_eq]
                  · exfalso
                    exact hif rfl
                exact h8
            have h := makespan_ge_each (m := 6) loads9 m11
            rw [h_loads9_m11] at h
            nlinarith [h_all_ge m11, h]
          calc
            (1 + gamma6) * PseudoLB6 σ5 = (1 + gamma6) * 1 := by rw [hlb]
            _ = gamma6 + 1 := gamma6_add_one_eq.symm
            _ ≤ algorithmMakespan 6 alg σ5 := h_mk

end OnlineScheduling
