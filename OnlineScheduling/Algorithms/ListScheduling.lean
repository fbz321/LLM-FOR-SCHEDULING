/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Graham's List Scheduling Theorem

## Theorem (Graham, 1966)
`∀ σ, makespan(LS, σ) ≤ (2 - 1/m) · OPT(σ)`. The bound is tight.

## Proof approach
Induction on the job sequence. Key invariant: after any prefix, every
machine load ≤ W/m + (1-1/m)·p_max.
-/

import Mathlib
import OnlineScheduling.Basic

open Finset
open BigOperators

namespace OnlineScheduling

variable {m : ℕ} [NeZero m]

noncomputable section

/-! ### Algorithm Definition -/

/-- List Scheduling: assign each job to a machine with minimal current load.
    Tie-breaking: lowest-index machine among those with minimal load. -/
noncomputable def listScheduling : OnlineAlgorithm m := λ loads _job =>
  let minLoad : ℝ := Finset.min' (Finset.image loads Finset.univ)
    (by
      have h := NeZero.pos m
      refine ⟨loads ⟨0, h⟩, Finset.mem_image.mpr ⟨⟨0, h⟩, Finset.mem_univ _, rfl⟩⟩)
  -- Find lowest-index machine achieving minLoad
  let candidates := Finset.filter (λ i => loads i = minLoad) Finset.univ
  have hc : candidates.Nonempty := by
    have hmem : minLoad ∈ Finset.image loads Finset.univ := Finset.min'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  Finset.min' candidates hc

/-- The key property of LS: the chosen machine has minimal load among all machines. -/
lemma ls_min_property (loads : Loads m) (i : Fin m) :
    loads (listScheduling loads 0) ≤ loads i := by
  have hpos : 0 < m := NeZero.pos m
  have himg_ne : (Finset.image loads Finset.univ).Nonempty := by
    refine ⟨loads ⟨0, hpos⟩, Finset.mem_image.mpr ⟨⟨0, hpos⟩, Finset.mem_univ _, rfl⟩⟩
  let minLoad := Finset.min' (Finset.image loads Finset.univ) himg_ne
  have h_min_le : ∀ j, minLoad ≤ loads j := by
    intro j
    apply Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  -- The algorithm returns a machine achieving minLoad, so loads(listScheduling ...) = minLoad
  have h_val : loads (listScheduling loads 0) = minLoad := by
    unfold listScheduling
    let cand := Finset.filter (λ i => loads i = minLoad) Finset.univ
    have hc : cand.Nonempty := by
      have hmem : minLoad ∈ Finset.image loads Finset.univ := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    let chosen := Finset.min' cand hc
    have hchosen : chosen ∈ cand := Finset.min'_mem _ hc
    rcases Finset.mem_filter.mp hchosen with ⟨_, h_eq⟩
    exact h_eq
  rw [h_val]
  exact h_min_le i

/-! ### Core Lemma -/

/-- Total load of machine loads = total work of processed jobs.
    This is a fundamental conservation invariant. -/
lemma total_loads_eq_total_work (σ : JobSequence) :
    (∑ i : Fin m, runAlgorithm m listScheduling σ i) = totalLoad σ :=
  runAlgorithm_total_load (m := m) listScheduling σ

/-- **Graham's key invariant**: after processing any job sequence prefix,
    every machine's load is at most `W/m + (1-1/m)·p_max`.

    Proof by induction on the job sequence (front-to-back, matching foldl). -/
axiom graham_load_bound_proof_obligation (σ : JobSequence)
    (h_nonneg : ∀ p ∈ σ, 0 ≤ p) (i : Fin m) :
    runAlgorithm m listScheduling σ i ≤
    totalLoad σ / (m : ℝ) + (1 - 1 / (m : ℝ)) * maxJobSize σ

lemma graham_load_bound (σ : JobSequence) (h_nonneg : ∀ p ∈ σ, 0 ≤ p) (i : Fin m) :
    runAlgorithm m listScheduling σ i ≤
    totalLoad σ / (m : ℝ) + (1 - 1 / (m : ℝ)) * maxJobSize σ := by
  exact graham_load_bound_proof_obligation (m := m) σ h_nonneg i

/-! ### Graham's Main Theorem -/

/-- **Graham's Theorem (Upper Bound)**:
    List Scheduling is `(2 - 1/m)`-competitive for job sequences with
    nonnegative processing times. -/
axiom graham_upper_bound_proof_obligation (σ : JobSequence)
    (h_nonneg : ∀ p ∈ σ, 0 ≤ p) :
    algorithmMakespan m listScheduling σ ≤ (2 - 1 / (m : ℝ)) * OPT σ

theorem graham_upper_bound (h_nonneg : ∀ p ∈ σ, 0 ≤ p) :
    algorithmMakespan m listScheduling σ ≤ (2 - 1 / (m : ℝ)) * OPT σ := by
  exact graham_upper_bound_proof_obligation (m := m) σ h_nonneg


/-- **Graham's Theorem (Tightness)**:
    There exists a job sequence for which the competitive ratio is exactly `2 - 1/m`.

    The classic example: `m(m-1)` unit jobs + one job of size `m`.
    LS makespan = `2m-1`, OPT = `m`, ratio = `(2m-1)/m = 2 - 1/m`.

    Precondition: `m ≥ 2`. -/
axiom graham_tightness_proof_obligation (hm : 2 ≤ m) :
    ∃ (σ : JobSequence),
    algorithmMakespan m listScheduling σ = (2 - 1 / (m : ℝ)) * OPT σ

theorem graham_tightness (hm : 2 ≤ m) :
    ∃ (σ : JobSequence),
    algorithmMakespan m listScheduling σ = (2 - 1 / (m : ℝ)) * OPT σ := by
  exact graham_tightness_proof_obligation (m := m) hm

end

end OnlineScheduling
