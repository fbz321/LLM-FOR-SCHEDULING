/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Lower Bound Framework for Online Scheduling

## Core Concepts
* **Adversary**: constructs a job sequence forcing any algorithm to achieve
  at least a target competitive ratio.
* **ForcesRatio**: the adversary forces ratio `c` if every algorithm has some
  job sequence where its makespan ≥ `c * OPT`.

## References
* Rudin & Chandrasekaran, SIAM J. Comput., 2003.
* Albers, SIAM J. Comput., 1999.
-/

import OnlineScheduling.Basic
import Mathlib.Data.Real.Basic

namespace OnlineScheduling

variable (m : ℕ) [NeZero m]

/-! ### Adversary Model -/

/-- An adversary strategy: given the job sequence presented so far,
    decide the next job to present (or `none` to stop). -/
structure Adversary where
  nextJob : List ℝ → Option ℝ
  maxSteps : ℕ
  bounded : ∀ (history : List ℝ), history.length ≤ maxSteps

/-- Generate the full job sequence produced by an adversary. The adversary
    repeatedly provides jobs until `none` or `maxSteps` is reached. -/
def generateSequence (adv : Adversary) : JobSequence :=
  -- Generate jobs iteratively: start with empty history,
  -- call adv.nextJob until we get none.
  let rec go (history : List ℝ) (steps : ℕ) : List ℝ :=
    if h : steps < adv.maxSteps then
      match adv.nextJob history with
      | none => history.reverse
      | some job => go (job :: history) (steps + 1)
    else
      history.reverse
  go [] 0
termination_by adv.maxSteps - steps
decreasing_by
  apply Nat.sub_lt_sub_left (h)
  omega

/-- Run an algorithm on the adversary-generated sequence and return
    `(makespan, OPT)` of the resulting instance. -/
def runAdversary (adv : Adversary) (alg : OnlineAlgorithm m) : ℝ × ℝ :=
  let σ := generateSequence adv
  (algorithmMakespan m alg σ, OPT σ)

/-! ### Lower Bound Theorem -/

/-- An adversary `adv` forces competitive ratio `c` if for every algorithm,
    there exists a job sequence where makespan ≥ `c · OPT`.

    Note: the adversary can choose the sequence adaptively based on
    the job history (but not the algorithm's state). -/
def ForcesRatio (adv : Adversary) (c : ℝ) : Prop :=
  ∀ (alg : OnlineAlgorithm m),
    ∃ (σ : JobSequence), algorithmMakespan m alg σ ≥ c * OPT σ

/-- If there exists an adversary forcing ratio `c` on nontrivial instances
    (OPT > 0), then for any `d < c`, no algorithm can be `d`-competitive. -/
theorem no_algorithm_better_than {c d : ℝ} (hcd : d < c)
    (h_force : ForcesRatio m adv c) (alg : OnlineAlgorithm m)
    (h_opt_pos : ∀ (σ : JobSequence), 0 < OPT σ) :
    ¬ IsCCompetitive m alg d := by
  have h_bad := h_force alg
  rcases h_bad with ⟨σ, h_bad_seq⟩
  have h_opt_gt0 : 0 < OPT σ := h_opt_pos σ
  dsimp [IsCCompetitive]
  intro h_competitive
  have h_alg_bound := h_competitive σ
  -- h_bad_seq:  c * OPT ≤ algorithmMakespan
  -- h_alg_bound: algorithmMakespan ≤ d * OPT
  -- Combined: c * OPT ≤ d * OPT → (c-d)*OPT ≤ 0,
  -- but c-d > 0 and OPT > 0 → contradiction
  nlinarith

end OnlineScheduling

