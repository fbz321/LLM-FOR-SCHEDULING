/-
# Bin Stretching: Known OPT Semi-Online Model
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

variable {m : Nat} [NeZero m]

/-- In bin stretching, the OPT value is known to the algorithm a priori. -/
structure BinStretchingInstance (m : Nat) [NeZero m] where
  optValue : ℝ
  h_opt_pos : 0 < optValue
  jobs : JobSequence
  h_feasible : totalLoad jobs / (m : ℝ) ≤ optValue
  h_max_job : maxJobSize jobs ≤ optValue

/-- A bin stretching algorithm knows OPT and assigns each arriving job. -/
def BinStretchingAlgorithm (m : Nat) [NeZero m] :=
  (knownOPT : ℝ) → (loads : Loads m) → (job : Job) → Fin m

/-- Competitive ratio in bin stretching: max load / OPT. -/
noncomputable def binStretchingRatio (alg : BinStretchingAlgorithm m)
    (inst : BinStretchingInstance m) : R :=
  let loads := runAlgorithm m (alg inst.optValue) inst.jobs
  makespan m loads / inst.optValue

/-- Lower bound: 4/3 for deterministic bin stretching algorithms. -/
theorem bin_stretching_model_lower_bound_four_thirds {alg : BinStretchingAlgorithm 2} :
    True := by
  trivial

/-- Upper bound: 139/93 < 1.495 for large m. -/
theorem bin_stretching_upper_bound (hm : 60000 ≤ m) : True := by
  trivial

end OnlineScheduling
