/-
Classic Online Scheduling: Adaptive Adversary Constructions for Small m

P2||Cmax: lower bound 3/2 (tight — List Scheduling is optimal)
P3||Cmax: lower bound 3/2 (valid; tight bound 5/3 requires layered adversary)
P4||Cmax: see Faigle.lean (1+√2/2) and Rudin.lean (√3, 1.88)

Each proof constructs the adversary sequence adaptively by simulating
the algorithm's decisions on a prefix, then branching on the outcome.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset

namespace OnlineScheduling

variable {m : Nat} [NeZero m]

noncomputable section

/-- `OPT [1, 1] = 1` on two machines. -/
private lemma opt_two_ones : OPT [1, 1] = (1 : ℝ) := by
  simpa using opt_of_identical_jobs (m := 2) (1 : ℝ) (by norm_num)

/-- `OPT [1, 1, 2] = 2` on two machines. -/
private lemma opt_two_ones_two : OPT [1, 1, 2] = (2 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) [1, 1, 2] (2 : ℝ)
  norm_num [totalLoad]

/-- P2||Cmax: for any deterministic online algorithm on 2 machines,
    there exists a job sequence forcing ratio ≥ 3/2. -/
theorem p2_Cmax_lower_bound (alg : OnlineAlgorithm 2) :
    ∃ (σ : JobSequence), algorithmMakespan 2 alg σ ≥ (3 / 2 : ℝ) * OPT σ := by
  have h_layer := layer_separation (m := 2) alg (1 : ℝ) (by norm_num)
  rcases h_layer with h_imbal | h_bal
  · use [1, 1]
    have h_opt1 : OPT [1, 1] = (1 : ℝ) := opt_two_ones
    have h_mk : (2 : ℝ) ≤ algorithmMakespan 2 alg [1, 1] := by
      dsimp [algorithmMakespan]
      simpa [h_opt1, algorithmMakespan] using h_imbal
    calc
      (3 / 2 : ℝ) * OPT [1, 1] = (3 / 2 : ℝ) * (1 : ℝ) := by rw [h_opt1]
      _ ≤ (2 : ℝ) := by norm_num
      _ ≤ algorithmMakespan 2 alg [1, 1] := h_mk
  · use [1, 1, 2]
    have h_run : runAlgorithm 2 alg [1, 1, 2] =
        step (m := 2) alg (runAlgorithm 2 alg [1, 1]) (2 : ℝ) := by
      change runAlgorithm 2 alg ([1, 1] ++ [2]) =
        step (m := 2) alg (runAlgorithm 2 alg [1, 1]) (2 : ℝ)
      exact runAlgorithm_append_singleton (m := 2) alg [1, 1] (2 : ℝ)
    let j : Fin 2 := alg (runAlgorithm 2 alg [1, 1]) (2 : ℝ)
    have h_bal' : ∀ i : Fin 2, runAlgorithm 2 alg [1, 1] i = (1 : ℝ) := by
      simpa using h_bal
    have h_loadj : step (m := 2) alg (runAlgorithm 2 alg [1, 1]) (2 : ℝ) j = (3 : ℝ) := by
      dsimp [step]
      dsimp [j]
      simp [h_bal']
      norm_num
    have h_mk : (3 : ℝ) ≤ algorithmMakespan 2 alg [1, 1, 2] := by
      dsimp [algorithmMakespan]
      rw [h_run]
      have h := makespan_ge_each (m := 2) (step (m := 2) alg (runAlgorithm 2 alg [1, 1]) (2 : ℝ)) j
      nlinarith [h_loadj, h]
    have h_opt2 : OPT [1, 1, 2] = (2 : ℝ) := opt_two_ones_two
    calc
      (3 / 2 : ℝ) * OPT [1, 1, 2] = (3 / 2 : ℝ) * (2 : ℝ) := by rw [h_opt2]
      _ ≤ (3 : ℝ) := by norm_num
      _ ≤ algorithmMakespan 2 alg [1, 1, 2] := h_mk

/-- `OPT [1, 1, 1] = 1` on three machines. -/
private lemma opt_three_ones : OPT [1, 1, 1] = (1 : ℝ) := by
  simpa using opt_of_identical_jobs (m := 3) (1 : ℝ) (by norm_num)

/-- `OPT [1, 1, 1, 2] = 2` on three machines. -/
private lemma opt_three_ones_two : OPT [1, 1, 1, 2] = (2 : ℝ) := by
  apply le_antisymm
  · have h_sched : totalLoad [1, 1, 1, 2] =
        (∑ i : Fin 3, (fun i : Fin 3 => if i = 0 then (2 : ℝ) else if i = 1 then (2 : ℝ) else (1 : ℝ)) i) := by
      simp [totalLoad, Fin.sum_univ_three]; norm_num
    have h_mk : makespan 3 (fun i : Fin 3 => if i = 0 then (2 : ℝ) else if i = 1 then (2 : ℝ) else (1 : ℝ)) = (2 : ℝ) := by
      apply le_antisymm
      · dsimp [makespan]
        exact Finset.sup'_le Finset.univ_nonempty
          (fun i : Fin 3 => if i = 0 then (2 : ℝ) else if i = 1 then (2 : ℝ) else (1 : ℝ))
          (by intro i hi; fin_cases i <;> norm_num)
      · have h := makespan_ge_each (m := 3)
          (fun i : Fin 3 => if i = 0 then (2 : ℝ) else if i = 1 then (2 : ℝ) else (1 : ℝ)) 0
        simpa using h
    exact le_trans (opt_le_of_schedule (m := 3) [1, 1, 1, 2]
      (fun i : Fin 3 => if i = 0 then (2 : ℝ) else if i = 1 then (2 : ℝ) else (1 : ℝ)) h_sched) (by rw [h_mk])
  · have h_max : (2 : ℝ) ≤ maxJobSize [1, 1, 1, 2] := by
      have hmem : (2 : ℝ) ∈ [1, 1, 1, 2] := by simp
      exact maxJobSize_ge_each [1, 1, 1, 2] (2 : ℝ) hmem
    have h := opt_ge_max_job [1, 1, 1, 2]
    nlinarith [h_max, h]

/-- P3||Cmax: for any deterministic algorithm on 3 machines,
    there exists a job sequence forcing ratio ≥ 3/2. -/
theorem p3_Cmax_lower_bound (alg : OnlineAlgorithm 3) :
    ∃ (σ : JobSequence), algorithmMakespan 3 alg σ ≥ (3 / 2 : ℝ) * OPT σ := by
  have h_layer := layer_separation (m := 3) alg (1 : ℝ) (by norm_num)
  rcases h_layer with h_imbal | h_bal
  · use [1, 1, 1]
    have h_opt1 : OPT [1, 1, 1] = (1 : ℝ) := opt_three_ones
    have h_mk : (2 : ℝ) ≤ algorithmMakespan 3 alg [1, 1, 1] := by
      dsimp [algorithmMakespan]
      simpa [h_opt1, algorithmMakespan] using h_imbal
    calc
      (3 / 2 : ℝ) * OPT [1, 1, 1] = (3 / 2 : ℝ) * (1 : ℝ) := by rw [h_opt1]
      _ ≤ (2 : ℝ) := by norm_num
      _ ≤ algorithmMakespan 3 alg [1, 1, 1] := h_mk
  · use [1, 1, 1, 2]
    have h_run : runAlgorithm 3 alg [1, 1, 1, 2] =
        step (m := 3) alg (runAlgorithm 3 alg [1, 1, 1]) (2 : ℝ) := by
      change runAlgorithm 3 alg ([1, 1, 1] ++ [2]) =
        step (m := 3) alg (runAlgorithm 3 alg [1, 1, 1]) (2 : ℝ)
      exact runAlgorithm_append_singleton (m := 3) alg [1, 1, 1] (2 : ℝ)
    let j : Fin 3 := alg (runAlgorithm 3 alg [1, 1, 1]) (2 : ℝ)
    have h_bal' : ∀ i : Fin 3, runAlgorithm 3 alg [1, 1, 1] i = (1 : ℝ) := by
      simpa using h_bal
    have h_loadj : step (m := 3) alg (runAlgorithm 3 alg [1, 1, 1]) (2 : ℝ) j = (3 : ℝ) := by
      dsimp [step]
      dsimp [j]
      simp [h_bal']
      norm_num
    have h_mk : (3 : ℝ) ≤ algorithmMakespan 3 alg [1, 1, 1, 2] := by
      dsimp [algorithmMakespan]
      rw [h_run]
      have h := makespan_ge_each (m := 3) (step (m := 3) alg (runAlgorithm 3 alg [1, 1, 1]) (2 : ℝ)) j
      nlinarith [h_loadj, h]
    have h_opt2 : OPT [1, 1, 1, 2] = (2 : ℝ) := opt_three_ones_two
    calc
      (3 / 2 : ℝ) * OPT [1, 1, 1, 2] = (3 / 2 : ℝ) * (2 : ℝ) := by rw [h_opt2]
      _ ≤ (3 : ℝ) := by norm_num
      _ ≤ algorithmMakespan 3 alg [1, 1, 1, 2] := h_mk

end

end OnlineScheduling
