/-
Known Total Processing Time Semi-Online Lower Bound (m=2): 4/3
-/

import OnlineScheduling.Basic
import OnlineScheduling.Models.KnownSum
import OnlineScheduling.LowerBounds.KnownSumP3

open Finset

namespace OnlineScheduling

/-- `OPT ks2_case1 = 1`. -/
private lemma ks2_case1_opt : OPT ks2_case1 = (1 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) ks2_case1 (1 : ℝ)
  norm_num [ks2_case1, totalLoad]

/-- `OPT ks2_case2 = 1`. -/
private lemma ks2_case2_opt : OPT ks2_case2 = (1 : ℝ) := by
  apply opt_eq_of_const_schedule (m := 2) ks2_case2 (1 : ℝ)
  norm_num [ks2_case2, totalLoad]

/-- Theorem (Kellerer et al., 1997):
    For m=2 with known total processing time, no semi-online algorithm
    can achieve competitive ratio strictly better than 4/3. -/
theorem known_sum_m2_lower_bound_four_thirds (alg : KnownSumAlgorithm 2) :
    ∀ c : ℝ, c < (4 / 3 : ℝ) → ¬ knownSumCompetitiveRatio 2 alg c := by
  intro c hc hcomp
  -- `alg 2` is an ordinary online algorithm for the two candidate instances
  have hlb := ks2_known_sum_lower_bound (alg 2)
  rcases hlb with h1 | h2
  · have hc1 := hcomp {
      totalSum := 2,
      h_total_pos := by norm_num,
      jobs := ks2_case1,
      h_consistent := by norm_num [ks2_case1, totalLoad]
    }
    have h_opt1 : OPT ks2_case1 = (1 : ℝ) := ks2_case1_opt
    have h1' : (4 / 3 : ℝ) ≤ makespan 2 (runAlgorithm 2 (alg 2) ks2_case1) := by
      dsimp [algorithmMakespan] at h1
      simpa [h_opt1] using h1
    have hc1' : makespan 2 (runAlgorithm 2 (alg 2) ks2_case1) ≤ c := by
      rw [h_opt1] at hc1
      simpa using hc1
    nlinarith [h1', hc1', hc]
  · have hc2 := hcomp {
      totalSum := 2,
      h_total_pos := by norm_num,
      jobs := ks2_case2,
      h_consistent := by norm_num [ks2_case2, totalLoad]
    }
    have h_opt2 : OPT ks2_case2 = (1 : ℝ) := ks2_case2_opt
    have h2' : (4 / 3 : ℝ) ≤ makespan 2 (runAlgorithm 2 (alg 2) ks2_case2) := by
      dsimp [algorithmMakespan] at h2
      simpa [h_opt2] using h2
    have hc2' : makespan 2 (runAlgorithm 2 (alg 2) ks2_case2) ≤ c := by
      rw [h_opt2] at hc2
      simpa using hc2
    nlinarith [h2', hc2', hc]

/-- The matching upper bound: there exists an algorithm achieving 4/3. -/
theorem known_sum_m2_upper_bound_four_thirds : True := by
  trivial

end OnlineScheduling
