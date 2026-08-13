/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Online Scheduling: Basic Definitions
-/

import Mathlib

open Finset
open BigOperators
open List

namespace OnlineScheduling

abbrev R := ℝ

/-! ### Jobs and Job Sequences -/

abbrev Job := ℝ
abbrev JobSequence := List Job

def totalLoad (σ : JobSequence) : ℝ := σ.sum

def maxJobSize (σ : JobSequence) : ℝ := σ.foldl max 0

private lemma foldl_max_nonneg (a : ℝ) (ha : 0 ≤ a) (σ : List ℝ) (h : ∀ x ∈ σ, 0 ≤ x) :
    0 ≤ List.foldl max a σ := by
  induction σ generalizing a with
  | nil => exact ha
  | cons p σ ih =>
      rw [List.foldl]
      have hp : 0 ≤ p := h p (by simp)
      have h_max : 0 ≤ max a p := by simp [ha, hp]
      have h_rest : ∀ x ∈ σ, 0 ≤ x := λ x hx => h x (by simp [hx])
      exact ih (max a p) h_max h_rest

private lemma foldl_max_mono {a b : ℝ} (hle : a ≤ b) (σ : List ℝ) :
    List.foldl max a σ ≤ List.foldl max b σ := by
  induction σ generalizing a b with
  | nil => exact hle
  | cons p σ ih =>
      simp [List.foldl]
      exact ih (max_le_max hle (le_refl p))

private lemma foldl_max_ge_acc (a : ℝ) (σ : List ℝ) : a ≤ List.foldl max a σ := by
  induction σ generalizing a with
  | nil => simp
  | cons p σ ih =>
      simp [List.foldl]
      exact le_trans (le_max_left _ _) (ih (max a p))

lemma maxJobSize_nonneg (σ : JobSequence) (h : ∀ p ∈ σ, 0 ≤ p) : 0 ≤ maxJobSize σ := by
  unfold maxJobSize
  exact foldl_max_nonneg 0 (le_refl 0) σ h

lemma maxJobSize_ge_each (σ : JobSequence) : ∀ p ∈ σ, p ≤ maxJobSize σ := by
  unfold maxJobSize
  induction σ with
  | nil => simp
  | cons q σ ih =>
      simp [List.foldl]
      constructor
      · exact le_trans (le_max_right 0 q) (foldl_max_ge_acc (max 0 q) σ)
      · intro a ha
        exact le_trans (ih a ha) (foldl_max_mono (le_max_left 0 q) σ)

/-! ### Machine Loads and Makespan -/

variable (m : ℕ) [NeZero m]

abbrev Loads := Fin m → ℝ

def makespan (loads : Loads m) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty loads

lemma makespan_ge_each (loads : Loads m) (i : Fin m) : loads i ≤ makespan m loads := by
  dsimp [makespan]
  apply Finset.le_sup'
  exact Finset.mem_univ i

lemma makespan_eq_some (loads : Loads m) : ∃ i : Fin m, loads i = makespan m loads := by
  dsimp [makespan]
  have h := Finset.exists_mem_eq_sup' Finset.univ_nonempty loads
  rcases h with ⟨i, _, hi⟩
  exact ⟨i, hi.symm⟩

lemma zero_loads_nonneg : 0 ≤ makespan m (λ _ : Fin m => 0) := by
  have h := makespan_ge_each (m := m) (λ _ : Fin m => 0) (0 : Fin m)
  simpa using h

/-! ### Online Algorithm -/

def OnlineAlgorithm := (loads : Loads m) → (job : Job) → Fin m

def step (alg : OnlineAlgorithm m) (loads : Loads m) (job : ℝ) : Loads m :=
  let machine := alg loads job
  fun i => if i = machine then loads i + job else loads i

def runAlgorithm (alg : OnlineAlgorithm m) (σ : JobSequence) : Loads m :=
  σ.foldl (step (m := m) alg) (λ _ => 0)

def algorithmMakespan (alg : OnlineAlgorithm m) (σ : JobSequence) : ℝ :=
  makespan m (runAlgorithm m alg σ)

private lemma sum_update_add (loads : Loads m) (j : Fin m) (p : ℝ) :
    (∑ i : Fin m, (if i = j then loads i + p else loads i)) = (∑ i : Fin m, loads i) + p := by
  calc
    (∑ i : Fin m, (if i = j then loads i + p else loads i))
        = (∑ i : Fin m, (loads i + (if i = j then p else 0))) := by
      refine Finset.sum_congr (by rfl) (λ x hx => ?_)
      by_cases h : x = j
      · subst h; simp
      · simp [h]
    _ = (∑ i : Fin m, loads i) + (∑ i : Fin m, (if i = j then p else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, loads i) + p := by simp

lemma sum_step (alg : OnlineAlgorithm m) (loads : Loads m) (job : ℝ) :
    (∑ i : Fin m, step (m := m) alg loads job i) = (∑ i : Fin m, loads i) + job := by
  dsimp [step]
  exact sum_update_add (m := m) loads (alg loads job) job

lemma sum_foldl_step (alg : OnlineAlgorithm m) (loads_before : Loads m) (tau : JobSequence) :
    (∑ i : Fin m, (tau.foldl (step (m := m) alg) loads_before i)) =
    (∑ i, loads_before i) + totalLoad tau := by
  induction' tau with p tau ih generalizing loads_before
  · simp [totalLoad]
  · rw [List.foldl_cons]
    have h_step := sum_step (m := m) alg loads_before p
    have h := ih (step (m := m) alg loads_before p)
    rw [h, h_step]
    simp [totalLoad, add_comm, add_left_comm, add_assoc]

lemma runAlgorithm_total_load (alg : OnlineAlgorithm m) (σ : JobSequence) :
    (∑ i : Fin m, runAlgorithm m alg σ i) = totalLoad σ := by
  simpa [runAlgorithm] using sum_foldl_step (m := m) alg (λ _ : Fin m => 0) σ

lemma runAlgorithm_append_singleton (alg : OnlineAlgorithm m) (σ : JobSequence) (p : Job) :
    runAlgorithm m alg (σ ++ [p]) = step (m := m) alg (runAlgorithm m alg σ) p := by
  rw [runAlgorithm, List.foldl_append]
  rfl

lemma runAlgorithm_snoc (alg : OnlineAlgorithm m) (σ : JobSequence) (p : Job) (hp : 0 ≤ p) (i : Fin m) :
    runAlgorithm m alg σ i ≤ runAlgorithm m alg (σ ++ [p]) i := by
  rw [runAlgorithm_append_singleton (m := m) alg σ p]
  dsimp [step]
  by_cases h : i = alg (runAlgorithm m alg σ) p
  · simp [h, hp]
  · simp [h]

lemma runAlgorithm_mono (alg : OnlineAlgorithm m) (σ₁ σ₃ : JobSequence) (h_nonneg : ∀ p ∈ σ₃, 0 ≤ p) :
    ∀ i, runAlgorithm m alg σ₁ i ≤ runAlgorithm m alg (σ₁ ++ σ₃) i := by
  induction' σ₃ with p σ₃ ih generalizing σ₁
  · simp
  · intro i
    have hp_nonneg : 0 ≤ p := h_nonneg p (by simp)
    have h_rest : ∀ q ∈ σ₃, 0 ≤ q := λ q hq => h_nonneg q (by simp [hq])
    rw [show σ₁ ++ (p :: σ₃) = (σ₁ ++ [p]) ++ σ₃ by simp]
    have h_step : runAlgorithm m alg σ₁ i ≤ runAlgorithm m alg (σ₁ ++ [p]) i :=
      runAlgorithm_snoc (m := m) alg σ₁ p hp_nonneg i
    have h_ih := ih (σ₁ := σ₁ ++ [p]) h_rest i
    exact le_trans h_step h_ih

/-! ### Offline Optimal Makespan (OPT) -/

opaque OPT (σ : JobSequence) : ℝ

axiom opt_ge_max_job (σ : JobSequence) : maxJobSize σ ≤ OPT σ
axiom opt_ge_avg_load (σ : JobSequence) : totalLoad σ / (m : ℝ) ≤ OPT σ

lemma opt_ge_both (σ : JobSequence) : max (maxJobSize σ) (totalLoad σ / (m : ℝ)) ≤ OPT σ :=
  max_le (opt_ge_max_job σ) (opt_ge_avg_load (m := m) σ)

lemma makespan_ge_average (loads : Loads m) :
    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ makespan m loads := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have h_each_le : ∀ i, loads i ≤ makespan m loads := makespan_ge_each (m := m) loads
  have h_sum_le : (Finset.sum Finset.univ loads) ≤ (m : ℝ) * makespan m loads := by
    calc
      (Finset.sum Finset.univ loads) ≤ (Finset.sum Finset.univ (fun _ => makespan m loads)) :=
        Finset.sum_le_sum (fun i _ => h_each_le i)
      _ = (m : ℝ) * makespan m loads := by simp
  refine calc
    (Finset.sum Finset.univ loads) / (m : ℝ) ≤ ((m : ℝ) * makespan m loads) / (m : ℝ) :=
      div_le_div_of_nonneg_right h_sum_le (by linarith)
    _ = makespan m loads := by field_simp [hm_pos.ne']

axiom opt_monotone (σ τ : JobSequence) (h_prefix : σ <+ τ) : OPT σ ≤ OPT τ
axiom opt_le_of_schedule (σ : JobSequence) (loads : Loads m)
    (h_valid : totalLoad σ = ∑ i : Fin m, loads i) : OPT σ ≤ makespan m loads

/-! ### Constant-load schedules -/

/-- The makespan of the constant load vector `c` on `m` machines is `c`. -/
lemma makespan_const (c : ℝ) : makespan m (fun _ : Fin m => c) = c := by
  dsimp [makespan]
  exact Finset.sup'_const Finset.univ_nonempty c

/-- If the total processing time is `m * c`, then the optimum is exactly `c`:
    giving every machine load `c` is an optimal schedule. -/
lemma opt_eq_of_const_schedule (σ : JobSequence) (c : ℝ)
    (h : totalLoad σ = (m : ℝ) * c) : OPT σ = c := by
  apply le_antisymm
  · have h_sched : totalLoad σ = (∑ i : Fin m, c) := by
      simp [h]
    exact le_trans (opt_le_of_schedule (m := m) σ (fun _ : Fin m => c) h_sched)
      (by rw [makespan_const (m := m) c])
  · have h_avg_load := opt_ge_avg_load (m := m) σ
    have h_avg : totalLoad σ / (m : ℝ) = c := by
      rw [h]
      field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast NeZero.ne m]
    nlinarith [h_avg_load, h_avg]

/-! ### Competitive Ratio -/

def IsCCompetitive (alg : OnlineAlgorithm m) (c : ℝ) : Prop :=
  ∀ (σ : JobSequence), algorithmMakespan m alg σ ≤ c * OPT σ

noncomputable def competitiveRatio (alg : OnlineAlgorithm m) : ℝ :=
  sInf {c : ℝ | IsCCompetitive m alg c}

lemma mem_competitive_set_iff (alg : OnlineAlgorithm m) (c : ℝ) :
    c ∈ {c : ℝ | IsCCompetitive m alg c} ↔ IsCCompetitive m alg c := by
  simp

lemma competitive_mono (alg : OnlineAlgorithm m) {c d : ℝ} (hc : IsCCompetitive m alg c)
    (hcd : c ≤ d) : IsCCompetitive m alg d := by
  intro σ
  have h := hc σ
  have h_opt_nonneg : 0 ≤ OPT σ := by
    have h_max_nonneg : 0 ≤ maxJobSize σ := by
      unfold maxJobSize; exact foldl_max_ge_acc (0 : ℝ) σ
    linarith [opt_ge_max_job σ, h_max_nonneg]
  nlinarith

/-! ### Nonnegativity Lemmas -/

lemma runAlgorithm_loads_nonneg (alg : OnlineAlgorithm m) (sigma : JobSequence)
    (h_nonneg : ∀ p ∈ sigma, 0 ≤ p) (i : Fin m) : 0 ≤ runAlgorithm m alg sigma i := by
  have h := runAlgorithm_mono (m := m) alg [] sigma h_nonneg i
  simpa [runAlgorithm] using h

lemma algorithmMakespan_nonneg (alg : OnlineAlgorithm m) (sigma : JobSequence)
    (h_nonneg : ∀ p ∈ sigma, 0 ≤ p) : 0 ≤ algorithmMakespan m alg sigma := by
  dsimp [algorithmMakespan]
  have h_loads_nonneg := runAlgorithm_loads_nonneg (m := m) alg sigma h_nonneg
  have h := makespan_ge_each (m := m) (runAlgorithm m alg sigma) 0
  have h0 : 0 ≤ runAlgorithm m alg sigma 0 := h_loads_nonneg 0
  exact le_trans h0 h

/-! ### Infrastructure Lemmas -/

lemma pigeonhole_all_ones {m : ℕ} (ns : Fin m → ℕ)
    (h_each : ∀ i, ns i ≤ 1) (h_sum : (∑ i, ns i) = m) (i : Fin m) : ns i = 1 := by
  by_contra! h_ne
  have h_i_lt_one : ns i < 1 := by
    have h_le := h_each i
    have h_ne' : ns i ≠ 1 := h_ne
    omega
  have h_i_zero : ns i = 0 := by omega
  have h_sum_lt : (∑ k : Fin m, ns k) < (∑ _k : Fin m, (1 : ℕ)) :=
    Finset.sum_lt_sum (fun k _ => h_each k) ⟨i, Finset.mem_univ i, by
      rw [h_i_zero]
      have h0 : (0 : ℕ) < 1 := by decide
      exact h0⟩
  have h_sum_one : (∑ _k : Fin m, (1 : ℕ)) = m := by simp
  rw [h_sum_one, h_sum] at h_sum_lt
  linarith

lemma algorithmMakespan_mono (alg : OnlineAlgorithm m) (sigma tau : JobSequence)
    (h_nonneg_tau : ∀ p ∈ tau, 0 ≤ p) :
    algorithmMakespan m alg sigma ≤ algorithmMakespan m alg (sigma ++ tau) := by
  have h := runAlgorithm_mono (m := m) alg sigma tau h_nonneg_tau
  dsimp [algorithmMakespan, makespan]
  refine Finset.sup'_le _ _ (λ i hi => ?_)
  have hi_le := h i
  exact le_trans hi_le (Finset.le_sup' (runAlgorithm m alg (sigma ++ tau)) hi)

lemma load_mono_on_prefix (alg : OnlineAlgorithm m) (sigma tau : JobSequence)
    (h_nonneg : ∀ p ∈ tau, 0 ≤ p) (i : Fin m) :
    runAlgorithm m alg sigma i ≤ runAlgorithm m alg (sigma ++ tau) i :=
  runAlgorithm_mono (m := m) alg sigma tau h_nonneg i


/-! ### Sound offline optimum, v2: concrete definition via assignments

**WARNING (2026-08-08):** the old opaque `OPT` and its four axioms above are
INCONSISTENT. `opt_le_of_schedule` accepts any load vector whose entries sum to
`totalLoad σ`; in particular the constant vector `λ _ => totalLoad σ / m`,
which yields `OPT σ ≤ totalLoad σ / m`. Together with `opt_ge_max_job` this
gives a contradiction for any sequence containing a job above the average load
(see `ProbeOPT.lean` at the repo root, which derives `False`).

All new formalization must use `optMakespan` below: it is defined concretely as
the minimum makespan over all job→machine assignments, and its characteristic
properties are theorems. The old axioms remain (quarantined) only until the
legacy files are migrated, after which they must be removed. -/

/-- Load vector induced by assigning each job of σ to a machine. -/
noncomputable def scheduleLoads (σ : JobSequence) (assign : Fin σ.length → Fin m) :
    Loads m :=
  fun j => ∑ i : Fin σ.length, if assign i = j then σ[i] else 0

/-- The assignment type is always inhabited (m ≥ 1). -/
private lemma univ_assign_nonempty (σ : JobSequence) :
    (Finset.univ : Finset (Fin σ.length → Fin m)).Nonempty :=
  ⟨fun _ => ⟨0, by exact_mod_cast NeZero.pos m⟩, Finset.mem_univ _⟩

/-- Offline optimal makespan on m machines: the minimum over all assignments.
    The assignment type is finite (m^n), so this is a genuine minimum. -/
noncomputable def optMakespan (σ : JobSequence) : ℝ :=
  Finset.univ.inf' (univ_assign_nonempty (m := m) σ)
    (fun a => makespan m (scheduleLoads (m := m) σ a))

private lemma getElem_mem_fin (σ : JobSequence) (i : Fin σ.length) : σ[i] ∈ σ :=
  List.mem_iff_getElem.mpr ⟨i.1, i.2, rfl⟩

/-- Any assignment witnesses the total load. -/
lemma sum_scheduleLoads (σ : JobSequence) (a : Fin σ.length → Fin m) :
    (∑ j : Fin m, scheduleLoads (m := m) σ a j) = totalLoad σ := by
  calc (∑ j : Fin m, scheduleLoads (m := m) σ a j)
      = ∑ i : Fin σ.length, ∑ j : Fin m, (if a i = j then σ[i] else 0) := by
        dsimp [scheduleLoads]
        rw [Finset.sum_comm]
  _ = ∑ i : Fin σ.length, σ[i] := by
        apply Finset.sum_congr rfl
        intro i _
        have hflip : (∑ j : Fin m, (if a i = j then σ[i] else 0)) =
            ∑ j : Fin m, (if j = a i then σ[i] else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : a i = j
          · rw [if_pos hj, if_pos hj.symm]
          · rw [if_neg hj, if_neg (fun h => hj h.symm)]
        rw [hflip, Finset.sum_ite_eq']
        simp
  _ = σ.sum := Fin.sum_univ_getElem σ
  _ = totalLoad σ := by dsimp [totalLoad]

/-- OPT ≤ makespan of any concrete assignment. -/
theorem optMakespan_le_schedule (σ : JobSequence) (a : Fin σ.length → Fin m) :
    optMakespan (m := m) σ ≤ makespan m (scheduleLoads (m := m) σ a) :=
  Finset.inf'_le (fun a => makespan m (scheduleLoads (m := m) σ a)) (Finset.mem_univ a)

/-- OPT ≤ makespan of any load vector that comes from an assignment. -/
theorem optMakespan_le_of_schedule (σ : JobSequence) (loads : Loads m)
    (a : Fin σ.length → Fin m) (ha : loads = scheduleLoads (m := m) σ a) :
    optMakespan (m := m) σ ≤ makespan m loads := by
  rw [ha]
  exact optMakespan_le_schedule (m := m) σ a

private lemma foldl_max_le {a x : ℝ} (σ : List ℝ) (ha : a ≤ x)
    (h : ∀ p ∈ σ, p ≤ x) : List.foldl max a σ ≤ x := by
  induction σ generalizing a with
  | nil => simpa using ha
  | cons p σ ih =>
      rw [List.foldl_cons]
      apply ih (max_le ha (h p (by simp)))
      intro q hq
      exact h q (by simp [hq])

private lemma maxJobSize_le_of_forall (σ : JobSequence) {x : ℝ} (h0 : 0 ≤ x)
    (h : ∀ p ∈ σ, p ≤ x) : maxJobSize σ ≤ x := by
  unfold maxJobSize
  exact foldl_max_le σ h0 h

/-- OPT ≥ largest job (for nonnegative jobs). -/
theorem optMakespan_ge_max_job (σ : JobSequence)
    (h_nonneg : ∀ p ∈ σ, 0 ≤ p) :
    maxJobSize σ ≤ optMakespan (m := m) σ := by
  apply Finset.le_inf'
  intro a _
  apply maxJobSize_le_of_forall
  · have h0 : 0 ≤ scheduleLoads (m := m) σ a 0 := by
      dsimp [scheduleLoads]
      apply Finset.sum_nonneg
      intro i _
      by_cases h : a i = 0
      · rw [if_pos h]
        exact h_nonneg σ[i] (getElem_mem_fin σ i)
      · rw [if_neg h]
    exact le_trans h0 (makespan_ge_each (m := m) _ 0)
  · intro p hp
    rcases List.mem_iff_getElem.mp hp with ⟨i, hi, hrfl⟩
    let iF : Fin σ.length := ⟨i, hi⟩
    rw [← hrfl]
    have hterm : σ[iF] ≤ scheduleLoads (m := m) σ a (a iF) := by
      dsimp [scheduleLoads]
      apply le_trans _ (Finset.sum_le_sum (f := fun k => if k = iF then σ[k] else 0) (fun k _ => ?_))
      · rw [Finset.sum_ite_eq']
        simp
      · by_cases hk : k = iF
        · simp [hk]
        · by_cases hcond : a k = a iF
          · rw [if_pos hcond, if_neg hk]
            exact h_nonneg σ[k] (getElem_mem_fin σ k)
          · rw [if_neg hcond, if_neg hk]
    exact le_trans hterm (makespan_ge_each (m := m) _ (a iF))

/-- OPT ≥ average load. -/
theorem optMakespan_ge_avg (σ : JobSequence) :
    totalLoad σ / (m : ℝ) ≤ optMakespan (m := m) σ := by
  apply Finset.le_inf'
  intro a _
  have h := makespan_ge_average (m := m) (scheduleLoads (m := m) σ a)
  rw [sum_scheduleLoads (m := m) σ a] at h
  exact h

/-- OPT ≥ 0 for nonnegative jobs. -/
theorem optMakespan_nonneg (σ : JobSequence) (h_nonneg : ∀ p ∈ σ, 0 ≤ p) :
    0 ≤ optMakespan (m := m) σ := by
  have h1 : 0 ≤ maxJobSize σ := maxJobSize_nonneg σ h_nonneg
  linarith [optMakespan_ge_max_job (m := m) σ h_nonneg]


/-! ### Assignments for concatenated sequences -/

/-- Combined assignment for a concatenated sequence: jobs of σ use `aσ`,
    jobs of τ use `aτ`. -/
noncomputable def appendAssign (σ τ : JobSequence)
    (aσ : Fin σ.length → Fin m) (aτ : Fin τ.length → Fin m) :
    Fin (σ ++ τ).length → Fin m :=
  fun i => if h : i.1 < σ.length then aσ ⟨i.1, h⟩
           else aτ ⟨i.1 - σ.length, by
             have h : (σ ++ τ).length = σ.length + τ.length := by simp
             omega⟩

lemma appendAssign_nil (τ : JobSequence)
    (aσ : Fin ([] : JobSequence).length → Fin m) (aτ : Fin τ.length → Fin m)
    (i : Fin τ.length) :
    appendAssign (m := m) [] τ aσ aτ i = aτ i := by
  dsimp [appendAssign]

lemma appendAssign_zero (p : Job) (σ τ : JobSequence)
    (aσ : Fin (p :: σ).length → Fin m) (aτ : Fin τ.length → Fin m)
    (i : Fin ((p :: σ) ++ τ).length) (hi : i.1 = 0) :
    appendAssign (m := m) (p :: σ) τ aσ aτ i = aσ ⟨0, by simp⟩ := by
  dsimp [appendAssign]
  rw [dif_pos (by simp [hi])]
  simp [hi]

lemma appendAssign_succ (p : Job) (σ τ : JobSequence)
    (aσ : Fin (p :: σ).length → Fin m) (aτ : Fin τ.length → Fin m)
    (k : Fin (σ ++ τ).length) :
    appendAssign (m := m) (p :: σ) τ aσ aτ (Fin.succ k) =
    appendAssign (m := m) σ τ (aσ ∘ Fin.succ) aτ k := by
  dsimp [appendAssign]
  by_cases hk : k.1 < σ.length
  · rw [dif_pos (by omega), dif_pos hk]
  · rw [dif_neg (by omega), dif_neg hk]
    congr 1
    exact Fin.ext (Nat.add_sub_add_right ..)

/-- Head/tail decomposition of the loads of a cons-sequence. -/
lemma scheduleLoads_cons (p : Job) (σ : JobSequence)
    (a : Fin (p :: σ).length → Fin m) (j : Fin m) :
    scheduleLoads (m := m) (p :: σ) a j =
    (if a 0 = j then p else 0) +
    scheduleLoads (m := m) σ (a ∘ Fin.succ) j := by
  dsimp [scheduleLoads]
  rw [Fin.sum_univ_succ]
  simp

/-- The loads of a concatenated sequence split into the loads of both halves. -/
lemma scheduleLoads_append (σ τ : JobSequence)
    (aσ : Fin σ.length → Fin m) (aτ : Fin τ.length → Fin m) (j : Fin m) :
    scheduleLoads (m := m) (σ ++ τ) (appendAssign (m := m) σ τ aσ aτ) j =
    scheduleLoads (m := m) σ aσ j + scheduleLoads (m := m) τ aτ j := by
  induction σ with
  | nil =>
      have hpoint : ∀ i : Fin τ.length,
          appendAssign (m := m) [] τ aσ aτ i = aτ i :=
        fun i => appendAssign_nil (m := m) τ aσ aτ i
      simp [scheduleLoads]
      exact Finset.sum_congr rfl (fun i _ => by simp [hpoint i])
  | cons p σ ih =>
      change scheduleLoads (m := m) (p :: (σ ++ τ))
          (appendAssign (m := m) (p :: σ) τ aσ aτ) j =
        scheduleLoads (m := m) (p :: σ) aσ j + scheduleLoads (m := m) τ aτ j
      rw [scheduleLoads_cons (m := m) p (σ ++ τ)
        (appendAssign (m := m) (p :: σ) τ aσ aτ) j]
      have htail : ∀ k : Fin (σ ++ τ).length,
          appendAssign (m := m) (p :: σ) τ aσ aτ (Fin.succ k) =
          appendAssign (m := m) σ τ (aσ ∘ Fin.succ) aτ k :=
        fun k => appendAssign_succ (m := m) p σ τ aσ aτ k
      have hsum : scheduleLoads (m := m) (σ ++ τ)
          (appendAssign (m := m) (p :: σ) τ aσ aτ ∘ Fin.succ) j =
          scheduleLoads (m := m) (σ ++ τ)
          (appendAssign (m := m) σ τ (aσ ∘ Fin.succ) aτ) j := by
        dsimp [scheduleLoads]
        apply Finset.sum_congr rfl
        intro k _
        simp [htail k]
      rw [hsum]
      rw [ih (aσ := aσ ∘ Fin.succ)]
      rw [scheduleLoads_cons (m := m) p σ aσ j]
      have hhead0 : appendAssign (m := m) (p :: σ) τ aσ aτ
          (0 : Fin (p :: (σ ++ τ)).length) = aσ 0 :=
        appendAssign_zero (m := m) p σ τ aσ aτ ⟨0, by simp⟩ (by rfl)
      rw [hhead0]
      ring
/-! ### Diagonal assignment for replicate sequences -/

/-- The diagonal assignment of `List.replicate m x`: job i goes to machine i. -/
noncomputable def diagAssignReplicate (x : ℝ) :
    Fin (List.replicate m x).length → Fin m :=
  fun i => ⟨i.1, by simpa [List.length_replicate] using i.2⟩

/-- Under the diagonal assignment every machine receives exactly one job. -/
lemma scheduleLoads_replicate_diag (x : ℝ) :
    scheduleLoads (m := m) (List.replicate m x) (diagAssignReplicate (m := m) x) =
    λ _ => x := by
  ext j
  dsimp only [scheduleLoads]
  conv_lhs => arg 2; ext i; simp [List.getElem_replicate]
  let i₀ : Fin (List.replicate m x).length := ⟨j.1, by simpa [List.length_replicate] using j.2⟩
  have hcond : ∀ i : Fin (List.replicate m x).length,
      (diagAssignReplicate (m := m) x i = j) ↔ i = i₀ := by
    intro i
    dsimp [diagAssignReplicate, i₀]
    constructor
    · intro h
      apply Fin.ext
      simpa using congrArg Fin.val h
    · intro h
      subst h
      apply Fin.ext
      rfl
  have hflip : (∑ i : Fin (List.replicate m x).length,
      if diagAssignReplicate (m := m) x i = j then x else 0) =
      ∑ i : Fin (List.replicate m x).length, if i = i₀ then x else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = i₀
    · rw [if_pos hi]
      exact if_pos ((hcond i).mpr hi)
    · rw [if_neg hi]
      exact if_neg (mt (hcond i).mp hi)
  rw [hflip, Finset.sum_ite_eq']
  simp
end OnlineScheduling
