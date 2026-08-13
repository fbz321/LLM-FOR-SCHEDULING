/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# Scenarios Model (Ergen, 2025)

Extension where each job belongs to a scenario, and jobs within the same
scenario have specific processing-time patterns. Lower bounds are derived
via hypergraph coloring connections.

## Reference

Ergen, E. "Online Makespan Scheduling Under Scenarios"
arXiv:2507.04016, 2025.
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

/-! ### Scenario Model -/

/-- A scenario is a set of processing times for `m` machines.
    Each machine has a prescribed processing time per scenario. -/
structure Scenario (m : ℕ) where
  processingTimes : Fin m → ℝ
  nonneg : ∀ i, 0 ≤ processingTimes i

/-- A scenario-aware job: belongs to one of `k` possible scenarios. -/
structure ScenarioJob (k : ℕ) (m : ℕ) where
  /-- Processing time in each possible scenario. -/
  times : Fin k → ℝ
  /-- All times nonnegative. -/
  nonneg : ∀ s, 0 ≤ times s
  /-- The true scenario (unknown to the algorithm). -/
  trueScenario : Fin k

end OnlineScheduling
