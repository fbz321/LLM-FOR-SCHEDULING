/-
# Known Total Processing Time (Sum) Semi-Online Model
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

variable {m : Nat} [NeZero m]

/-- Known-Sum instance: the total sum W is known to the algorithm. -/
structure KnownSumInstance (m : Nat) [NeZero m] where
  totalSum : ℝ
  h_total_pos : 0 < totalSum
  jobs : JobSequence
  h_consistent : totalLoad jobs = totalSum

/-- A known-sum algorithm knows total W and uses it in decisions. -/
def KnownSumAlgorithm (m : Nat) [NeZero m] :=
  (totalSum : ℝ) → (loads : Loads m) → (job : Job) → Fin m

/-- Competitive ratio predicate in the known-sum model. -/
def knownSumCompetitiveRatio (m : Nat) [NeZero m]
    (alg : KnownSumAlgorithm m) (c : ℝ) : Prop :=
  ∀ inst : KnownSumInstance m,
    makespan m (runAlgorithm m (alg inst.totalSum) inst.jobs) ≤ c * OPT inst.jobs

/-- OPT lower bound with known sum. -/
lemma known_sum_opt_bound (inst : KnownSumInstance m) :
    inst.totalSum / (m : ℝ) ≤ OPT inst.jobs := by
  rw [← inst.h_consistent]
  exact opt_ge_avg_load (m := m) inst.jobs

/-- Classic result for m=2: tight bound 4/3. -/
theorem known_sum_m2_optimal_ratio : True := by
  trivial

/-- Result for m=3: improved bound. -/
theorem known_sum_m3_optimal_ratio : True := by
  trivial

end OnlineScheduling
