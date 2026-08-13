/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Scheduling with Testing (Albers & Eckl, 2021)

Extension of online scheduling where each job has an unknown true processing
time, but the scheduler can optionally "test" a job (at cost `s_j`) to reveal
its true processing time before deciding where to schedule it.

## Model

Each job `j` has:
- `p_j`: true processing time (unknown until tested)
- `s_j`: testing time (known)
- The scheduler can either:
  1. Schedule immediately (without testing): assign to a machine, pay `p_j`
  2. Test first: spend `s_j`, learn `p_j`, then schedule

## Reference

Albers, S. & Eckl, A.
"Scheduling with Testing on Multiple Identical Parallel Machines"
arXiv:2105.02052, 2021.
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

/-! ### Job with Testing -/

/-- A job in the testing model: known testing time, unknown true processing time. -/
structure JobWithTest where
  /-- Testing time (known a priori). -/
  testTime : ℝ
  /-- True processing time (unknown until tested). -/
  trueTime : ℝ
  /-- All times are nonnegative. -/
  nonneg : 0 ≤ testTime ∧ 0 ≤ trueTime

/-- A job sequence in the testing model. -/
abbrev TestJobSequence := List JobWithTest

/-! ### Testing Strategies -/

/-- Decision after seeing a job: test it or schedule it immediately. -/
inductive TestingDecision
  | test
  | scheduleNow

/-- A testing-aware online algorithm: decides whether to test and where to schedule. -/
def TestingAlgorithm (m : ℕ) [NeZero m] :=
  (loads : Loads m) → (job : JobWithTest) → TestingDecision × Fin m

end OnlineScheduling
