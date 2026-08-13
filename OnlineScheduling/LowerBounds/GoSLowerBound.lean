/- Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

Grade of Service Online Lower Bound: 5/3 for m = 2 (Park, Chang & Lee, 2006).

We formalize Lemma 1 of the paper as an adaptive adversary over every
GoS-respecting deterministic algorithm.  Machine 0 is the "first" machine
(accepts both GoS levels); machine 1 accepts only g = two jobs.

  * two unit jobs with g = two:
      - both on one machine   -> makespan 2 vs OPT 1 (ratio 2);
      - split between machines ->
  * a third unit job with g = two:
      - on machine 0 -> present (3, g = one): makespan 5 vs OPT 3;
      - on machine 1 -> present (3, g = two):
          + on machine 1 -> makespan 5 vs OPT 3;
          + on machine 0 -> present (6, g = one): makespan 10 vs OPT 6.

Every branch satisfies makespan / OPT ≥ 5/3. -/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open Finset

namespace OnlineScheduling

inductive LBGoSLevel | one | two deriving DecidableEq, Repr

structure GoSJob where
  p : ℝ
  g : LBGoSLevel
  h_nonneg : 0 ≤ p

def gos_to_jobs (gs : List GoSJob) : List ℝ := gs.map GoSJob.p

/-- Unit-size job with g = two. -/
def gos_job_one_two : GoSJob :=
  { p := 1, g := LBGoSLevel.two, h_nonneg := by norm_num }

/-- Size-3 job with g = two. -/
def gos_job_three_two : GoSJob :=
  { p := 3, g := LBGoSLevel.two, h_nonneg := by norm_num }

/-- Size-3 job with g = one. -/
def gos_job_three_one : GoSJob :=
  { p := 3, g := LBGoSLevel.one, h_nonneg := by norm_num }

/-- Size-6 job with g = one. -/
def gos_job_six_one : GoSJob :=
  { p := 6, g := LBGoSLevel.one, h_nonneg := by norm_num }

def gos_branch_A : List GoSJob := [gos_job_one_two, gos_job_one_two]

def gos_branch_B1 : List GoSJob :=
  [gos_job_one_two, gos_job_one_two, gos_job_one_two, gos_job_three_one]

def gos_branch_B2a : List GoSJob :=
  [gos_job_one_two, gos_job_one_two, gos_job_one_two, gos_job_three_two]

def gos_branch_B2b : List GoSJob :=
  [gos_job_one_two, gos_job_one_two, gos_job_one_two, gos_job_three_two,
    gos_job_six_one]

lemma gos_opt_A : OPT (gos_to_jobs gos_branch_A) = (1 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) (gos_to_jobs gos_branch_A) (1 : ℝ)
  norm_num [gos_to_jobs, gos_branch_A, gos_job_one_two, totalLoad]

lemma gos_opt_B1 : OPT (gos_to_jobs gos_branch_B1) = (3 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) (gos_to_jobs gos_branch_B1) (3 : ℝ)
  norm_num [gos_to_jobs, gos_branch_B1, gos_job_one_two, gos_job_three_one, totalLoad]

lemma gos_opt_B2a : OPT (gos_to_jobs gos_branch_B2a) = (3 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) (gos_to_jobs gos_branch_B2a) (3 : ℝ)
  norm_num [gos_to_jobs, gos_branch_B2a, gos_job_one_two, gos_job_three_two, totalLoad]

lemma gos_opt_B2b : OPT (gos_to_jobs gos_branch_B2b) = (6 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) (gos_to_jobs gos_branch_B2b) (6 : ℝ)
  norm_num [gos_to_jobs, gos_branch_B2b, gos_job_one_two, gos_job_three_two,
    gos_job_six_one, totalLoad]

/-! ### GoS-respecting algorithm model -/

/-- A deterministic online algorithm for two-machine GoS scheduling.
    Machine 0 (the "first" machine) accepts every job; machine 1 accepts only
    g = two jobs.  `choose` returns the machine for a job and `respects`
    enforces that g = one jobs are scheduled on machine 0. -/
structure GoSAlgorithm2 where
  choose : Loads 2 → ℝ → LBGoSLevel → Fin 2
  respects : ∀ (loads : Loads 2) (p : ℝ), choose loads p LBGoSLevel.one = (0 : Fin 2)

/-- One scheduling step: add `job.p` to the machine chosen by the algorithm. -/
def gosStep (alg : GoSAlgorithm2) (loads : Loads 2) (job : GoSJob) : Loads 2 :=
  let machine := alg.choose loads job.p job.g
  fun i => if i = machine then loads i + job.p else loads i

/-- Run a GoS algorithm on a list of GoS jobs, starting from zero loads. -/
def gosRunAlgorithm (alg : GoSAlgorithm2) (gs : List GoSJob) : Loads 2 :=
  gs.foldl (fun loads job => gosStep alg loads job) (fun _ : Fin 2 => 0)

/-- Makespan of the schedule produced by a GoS algorithm. -/
def gosAlgorithmMakespan (alg : GoSAlgorithm2) (gs : List GoSJob) : ℝ :=
  makespan 2 (gosRunAlgorithm alg gs)

/-- A GoS algorithm viewed as a plain algorithm on g = two jobs. -/
private def gosPlainAlg (alg : GoSAlgorithm2) : OnlineAlgorithm 2 :=
  fun loads p => alg.choose loads p LBGoSLevel.two

/-- A `Fin 2` is either machine 0 or machine 1. -/
private lemma fin2_zero_or_one (i : Fin 2) : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  fin_cases i <;> simp

/-- A g = one job is forced onto machine 0. -/
private lemma gos_g1_machine (alg : GoSAlgorithm2) (loads : Loads 2) (p : ℝ) :
    alg.choose loads p LBGoSLevel.one = (0 : Fin 2) :=
  alg.respects loads p

/-- Scheduling a job on the machine the algorithm chose increases that
    machine's load by `job.p`. -/
private lemma gos_step_load (alg : GoSAlgorithm2) (loads : Loads 2) (job : GoSJob) (i : Fin 2)
    (h : alg.choose loads job.p job.g = i) :
    gosStep alg loads job i = loads i + job.p := by
  simp [gosStep, h]

/-- Scheduling a job on a machine the algorithm did not choose leaves that
    machine's load unchanged. -/
private lemma gos_step_load_other (alg : GoSAlgorithm2) (loads : Loads 2) (job : GoSJob)
    (i : Fin 2) (h : i ≠ alg.choose loads job.p job.g) :
    gosStep alg loads job i = loads i := by
  simp [gosStep, h]

private lemma gos_run_A (alg : GoSAlgorithm2) :
    gosRunAlgorithm alg gos_branch_A = runAlgorithm 2 (gosPlainAlg alg) [1, 1] := by
  rfl

private lemma gos_run_B1 (alg : GoSAlgorithm2) :
    gosRunAlgorithm alg gos_branch_B1 =
      gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
        gos_job_three_one := by
  rfl

private lemma gos_run_B2a (alg : GoSAlgorithm2) :
    gosRunAlgorithm alg gos_branch_B2a =
      gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
        gos_job_three_two := by
  rfl

private lemma gos_run_B2b (alg : GoSAlgorithm2) :
    gosRunAlgorithm alg gos_branch_B2b =
      gosStep alg (gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A)
        gos_job_one_two) gos_job_three_two) gos_job_six_one := by
  rfl

/-- Load of machine 0 at the end of branch B1 is 5, when jobs 1, 2 are split
    and job 3 (g = two) went to machine 0. -/
private lemma gos_load_B1_m0 (alg : GoSAlgorithm2)
    (h_split : ∀ i : Fin 2, gosRunAlgorithm alg gos_branch_A i = (1 : ℝ))
    (h3 : alg.choose (gosRunAlgorithm alg gos_branch_A) (1 : ℝ) LBGoSLevel.two =
      (0 : Fin 2)) :
    gosRunAlgorithm alg gos_branch_B1 (0 : Fin 2) = (5 : ℝ) := by
  rw [gos_run_B1]
  have h_l3 : gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (0 : Fin 2) = (2 : ℝ) := by
    have h3' : alg.choose (gosRunAlgorithm alg gos_branch_A) gos_job_one_two.p
        gos_job_one_two.g = (0 : Fin 2) := by
      simpa [gos_job_one_two] using h3
    rw [gos_step_load alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (0 : Fin 2) h3']
    simp [gos_job_one_two, h_split]
    norm_num
  have h4' : alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
      gos_job_three_one.p gos_job_three_one.g = (0 : Fin 2) := by
    simpa [gos_job_three_one] using
      gos_g1_machine alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
        (3 : ℝ)
  rw [gos_step_load alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
    gos_job_three_one (0 : Fin 2) h4']
  rw [h_l3]
  simp [gos_job_three_one]
  norm_num

/-- Load of machine 1 at the end of branch B2a is 5, when jobs 1, 2 are split,
    job 3 (g = two) went to machine 1 and job 4 (g = two) went to machine 1. -/
private lemma gos_load_B2a_m1 (alg : GoSAlgorithm2)
    (h_split : ∀ i : Fin 2, gosRunAlgorithm alg gos_branch_A i = (1 : ℝ))
    (h3 : alg.choose (gosRunAlgorithm alg gos_branch_A) (1 : ℝ) LBGoSLevel.two =
      (1 : Fin 2))
    (h4 : alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
      (3 : ℝ) LBGoSLevel.two = (1 : Fin 2)) :
    gosRunAlgorithm alg gos_branch_B2a (1 : Fin 2) = (5 : ℝ) := by
  rw [gos_run_B2a]
  have h_l3 : gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (1 : Fin 2) = (2 : ℝ) := by
    have h3' : alg.choose (gosRunAlgorithm alg gos_branch_A) gos_job_one_two.p
        gos_job_one_two.g = (1 : Fin 2) := by
      simpa [gos_job_one_two] using h3
    rw [gos_step_load alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (1 : Fin 2) h3']
    simp [gos_job_one_two, h_split]
    norm_num
  have h4' : alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
      gos_job_three_two.p gos_job_three_two.g = (1 : Fin 2) := by
    simpa [gos_job_three_two] using h4
  rw [gos_step_load alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
    gos_job_three_two (1 : Fin 2) h4']
  rw [h_l3]
  simp [gos_job_three_two]
  norm_num

/-- Load of machine 0 at the end of branch B2b is 10, when jobs 1, 2 are split,
    job 3 (g = two) went to machine 1 and job 4 (g = two) went to machine 0. -/
private lemma gos_load_B2b_m0 (alg : GoSAlgorithm2)
    (h_split : ∀ i : Fin 2, gosRunAlgorithm alg gos_branch_A i = (1 : ℝ))
    (h3 : alg.choose (gosRunAlgorithm alg gos_branch_A) (1 : ℝ) LBGoSLevel.two =
      (1 : Fin 2))
    (h4 : alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
      (3 : ℝ) LBGoSLevel.two = (0 : Fin 2)) :
    gosRunAlgorithm alg gos_branch_B2b (0 : Fin 2) = (10 : ℝ) := by
  rw [gos_run_B2b]
  have h_l3_0 : gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (0 : Fin 2) = (1 : ℝ) := by
    have h3' : alg.choose (gosRunAlgorithm alg gos_branch_A) gos_job_one_two.p
        gos_job_one_two.g = (1 : Fin 2) := by
      simpa [gos_job_one_two] using h3
    have h3ne : (0 : Fin 2) ≠ alg.choose (gosRunAlgorithm alg gos_branch_A)
        gos_job_one_two.p gos_job_one_two.g := by
      intro hbad
      rw [h3'] at hbad
      norm_num at hbad
    rw [gos_step_load_other alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two
      (0 : Fin 2) h3ne]
    simp [h_split]
  have h_l4_0 : gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A)
      gos_job_one_two) gos_job_three_two (0 : Fin 2) = (4 : ℝ) := by
    have h4' : alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
        gos_job_three_two.p gos_job_three_two.g = (0 : Fin 2) := by
      simpa [gos_job_three_two] using h4
    rw [gos_step_load alg (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
      gos_job_three_two (0 : Fin 2) h4']
    rw [h_l3_0]
    simp [gos_job_three_two]
    norm_num
  have h5' : alg.choose (gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A)
      gos_job_one_two) gos_job_three_two) gos_job_six_one.p gos_job_six_one.g =
      (0 : Fin 2) := by
    simpa [gos_job_six_one] using
      gos_g1_machine alg (gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A)
        gos_job_one_two) gos_job_three_two) (6 : ℝ)
  rw [gos_step_load alg (gosStep alg (gosStep alg (gosRunAlgorithm alg gos_branch_A)
    gos_job_one_two) gos_job_three_two) gos_job_six_one (0 : Fin 2) h5']
  rw [h_l4_0]
  simp [gos_job_six_one]
  norm_num

/-- If a machine ends with load at least `v`, then the makespan is at least `v`. -/
private lemma gos_makespan_ge (loads : Loads 2) (i : Fin 2) (v : ℝ) (h : v ≤ loads i) :
    v ≤ makespan 2 loads :=
  le_trans h (makespan_ge_each (m := 2) loads i)

/-- GoS online lower bound 5/3 (Park, Chang & Lee 2006, Lemma 1):
    every deterministic GoS-respecting algorithm has a job sequence with
    makespan ≥ (5/3) · OPT. -/
theorem gos_online_lower_bound_five_thirds (alg : GoSAlgorithm2) :
    ∃ gs : List GoSJob, gosAlgorithmMakespan alg gs ≥ (5 / 3 : ℝ) * OPT (gos_to_jobs gs) := by
  have h_layer := layer_separation (m := 2) (gosPlainAlg alg) (1 : ℝ) (by norm_num)
  rcases h_layer with h_imbal | h_bal
  · refine ⟨gos_branch_A, ?_⟩
    have h_mkA : (2 : ℝ) ≤ gosAlgorithmMakespan alg gos_branch_A := by
      dsimp [gosAlgorithmMakespan]
      change (2 : ℝ) ≤ makespan 2 (runAlgorithm 2 (gosPlainAlg alg) [1, 1])
      have h_opt1 : OPT [1, 1] = (1 : ℝ) := by
        simpa [gos_to_jobs, gos_branch_A, gos_job_one_two] using gos_opt_A
      calc
        (2 : ℝ) = 2 * (1 : ℝ) := by norm_num
        _ = 2 * OPT [1, 1] := by rw [h_opt1]
        _ ≤ makespan 2 (runAlgorithm 2 (gosPlainAlg alg) [1, 1]) := by
          simpa [algorithmMakespan] using h_imbal
    calc
      (5 / 3 : ℝ) * OPT (gos_to_jobs gos_branch_A) = (5 / 3 : ℝ) * (1 : ℝ) := by
        rw [gos_opt_A]
      _ ≤ (2 : ℝ) := by norm_num
      _ ≤ gosAlgorithmMakespan alg gos_branch_A := h_mkA
  · have h_split : ∀ i : Fin 2, gosRunAlgorithm alg gos_branch_A i = (1 : ℝ) := by
      intro i
      rw [gos_run_A]
      exact h_bal i
    rcases fin2_zero_or_one
      (alg.choose (gosRunAlgorithm alg gos_branch_A) (1 : ℝ) LBGoSLevel.two) with h3 | h3
    · -- job 3 (g = two) on machine 0: branch B1
      refine ⟨gos_branch_B1, ?_⟩
      have h_load : gosRunAlgorithm alg gos_branch_B1 (0 : Fin 2) = (5 : ℝ) :=
        gos_load_B1_m0 alg h_split h3
      have h_mk : (5 : ℝ) ≤ gosAlgorithmMakespan alg gos_branch_B1 := by
        dsimp [gosAlgorithmMakespan]
        exact gos_makespan_ge (gosRunAlgorithm alg gos_branch_B1) (0 : Fin 2) (5 : ℝ)
          (by rw [h_load])
      calc
        (5 / 3 : ℝ) * OPT (gos_to_jobs gos_branch_B1) = (5 / 3 : ℝ) * (3 : ℝ) := by
          rw [gos_opt_B1]
        _ ≤ (5 : ℝ) := by norm_num
        _ ≤ gosAlgorithmMakespan alg gos_branch_B1 := h_mk
    · -- job 3 (g = two) on machine 1: branch on job 4 (g = two)
      rcases fin2_zero_or_one
        (alg.choose (gosStep alg (gosRunAlgorithm alg gos_branch_A) gos_job_one_two)
          (3 : ℝ) LBGoSLevel.two) with h4 | h4
      · -- job 4 on machine 0: branch B2b
        refine ⟨gos_branch_B2b, ?_⟩
        have h_load : gosRunAlgorithm alg gos_branch_B2b (0 : Fin 2) = (10 : ℝ) :=
          gos_load_B2b_m0 alg h_split h3 h4
        have h_mk : (10 : ℝ) ≤ gosAlgorithmMakespan alg gos_branch_B2b := by
          dsimp [gosAlgorithmMakespan]
          exact gos_makespan_ge (gosRunAlgorithm alg gos_branch_B2b) (0 : Fin 2) (10 : ℝ)
            (by rw [h_load])
        calc
          (5 / 3 : ℝ) * OPT (gos_to_jobs gos_branch_B2b) = (5 / 3 : ℝ) * (6 : ℝ) := by
            rw [gos_opt_B2b]
          _ ≤ (10 : ℝ) := by norm_num
          _ ≤ gosAlgorithmMakespan alg gos_branch_B2b := h_mk
      · -- job 4 on machine 1: branch B2a
        refine ⟨gos_branch_B2a, ?_⟩
        have h_load : gosRunAlgorithm alg gos_branch_B2a (1 : Fin 2) = (5 : ℝ) :=
          gos_load_B2a_m1 alg h_split h3 h4
        have h_mk : (5 : ℝ) ≤ gosAlgorithmMakespan alg gos_branch_B2a := by
          dsimp [gosAlgorithmMakespan]
          exact gos_makespan_ge (gosRunAlgorithm alg gos_branch_B2a) (1 : Fin 2) (5 : ℝ)
            (by rw [h_load])
        calc
          (5 / 3 : ℝ) * OPT (gos_to_jobs gos_branch_B2a) = (5 / 3 : ℝ) * (3 : ℝ) := by
            rw [gos_opt_B2a]
          _ ≤ (5 : ℝ) := by norm_num
          _ ≤ gosAlgorithmMakespan alg gos_branch_B2a := h_mk

end OnlineScheduling
