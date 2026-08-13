/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Competitive Ratio: Properties and Utilities

Lemmas for reasoning about competitive ratios, including composition,
known bounds, and helper tactics.
-/

import Mathlib
import OnlineScheduling.Basic

open OnlineScheduling

namespace OnlineScheduling

/-! ### Two-machine sharp bounds

For `m = 2` and `m = 3`, List Scheduling is known to be optimal, achieving
competitive ratios `3/2` and `5/3` respectively. -/

/-- For `m = 2`, the optimal deterministic competitive ratio is `3/2`.
    This is achieved by List Scheduling. -/
noncomputable def m2_opt_ratio : ℝ := 3/2

/-- For `m = 3`, the optimal deterministic competitive ratio is `5/3`.
    This is achieved by List Scheduling. -/
noncomputable def m3_opt_ratio : ℝ := 5/3

/-! ### Known Bounds

Summary of known upper and lower bounds from the literature
(Rudin 2003, Table 1.1). -/

/-- Graham's upper bound for List Scheduling. -/
noncomputable def graham_ratio (m : ℕ) : ℝ := 2 - 1 / (m : ℝ)

/-- Albers' M2 upper bound — the best known for general `m`. -/
noncomputable def albers_m2_ratio : ℝ := 1.923

/-- Fleischer-Wahl MR upper bound — asymptotically the best known. -/
noncomputable def fleischer_wahl_mr_ratio : ℝ := 1.9201

/-- Rudin's lower bound — no deterministic algorithm can do better than this. -/
noncomputable def rudin_lower_bound : ℝ := 1.88

/-- Albers' lower bound for large `m`. -/
noncomputable def albers_lower_bound : ℝ := 1.852

/-- Faigle-Kern-Turan lower bound for `m ≥ 4`. -/
noncomputable def faigle_lower_bound : ℝ := 1 + Real.sqrt 2 / 2
-- = (1 + √2)/2 ≈ 1.7071

/-! ### Basic Properties -/

/-- If an algorithm is `c`-competitive, then every job sequence has makespan
    bounded by `c * OPT`. -/
lemma competitive_implies_bounded {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)
    (hc : IsCCompetitive m alg c) (σ : JobSequence) :
    algorithmMakespan m alg σ ≤ c * OPT σ := hc σ

/-- The competitive ratio is at least 1 for any algorithm.
    (No algorithm can have `makespan < OPT`.) -/
lemma competitive_ratio_ge_one {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (c : ℝ)
    (hc : IsCCompetitive m alg c) : 1 ≤ c := by
  let sigma : JobSequence := [1]
  let loadsBefore : Loads m := fun _ => 0
  let j : Fin m := alg loadsBefore 1
  have h_run : runAlgorithm m alg sigma = step (m := m) alg loadsBefore 1 := by
    simp [sigma, runAlgorithm, loadsBefore]
  have h_load_j : runAlgorithm m alg sigma j = 1 := by
    rw [h_run]
    simp [step, loadsBefore, j]
  have h_makespan_ge : 1 ≤ algorithmMakespan m alg sigma := by
    dsimp [algorithmMakespan]
    have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) j
    simpa [h_load_j] using h
  have h_opt_le : OPT sigma ≤ 1 := by
    let optLoads : Loads m := fun i => if i = j then (1 : ℝ) else 0
    have h_total : totalLoad sigma = ∑ i : Fin m, optLoads i := by
      have h_sum : (∑ i : Fin m, optLoads i) = (1 : ℝ) := by
        simp [optLoads]
      simp [sigma, totalLoad, h_sum]
    have h_makespan : makespan m optLoads = (1 : ℝ) := by
      apply le_antisymm
      · dsimp [makespan]
        apply Finset.sup'_le
        intro i _
        by_cases hij : i = j <;> simp [optLoads, hij]
      · have h := makespan_ge_each (m := m) optLoads j
        simpa [optLoads] using h
    have h := opt_le_of_schedule (m := m) sigma optLoads h_total
    simpa [h_makespan] using h
  have h_opt_ge : 1 ≤ OPT sigma := by
    have h_max : maxJobSize sigma = (1 : ℝ) := by
      simp [sigma, maxJobSize]
    have h := opt_ge_max_job sigma
    simpa [h_max] using h
  have h_bound := hc sigma
  have h_opt_eq : OPT sigma = 1 := le_antisymm h_opt_le h_opt_ge
  nlinarith

end OnlineScheduling
