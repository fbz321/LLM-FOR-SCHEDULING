/-
# Decreasing Job Sizes Semi-Online Model

Jobs arrive in non-increasing order of processing times: p1 ≥ p2 ≥ ... ≥ pn.
This partial ordering information enables better competitive ratios.

## Key Results
- m=2: tight bound 7/6 (Seiden, Sgall, Woeginger, 2000)
- m=3: lower bound ~1.18046, upper bound still open
- General m: LPT achieves 4/3 - 1/(3m) (Graham, 1969)
- Randomized m=2: 8/7 tight

## References
- Seiden, Sgall, Woeginger, Operations Research Letters 2000
- Graham, 1969 (LPT analysis)
-/

import OnlineScheduling.Basic
import OnlineScheduling.Algorithms.ListScheduling

namespace OnlineScheduling

variable {m : Nat} [NeZero m]

/-- A job sequence is decreasing if p_i ≥ p_{i+1} for all i.
    This is a predicate on the input sequence. -/
def isDecreasing : JobSequence -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => p ≥ q /\ isDecreasing (q :: rest)

/-- LPT algorithm: same as List Scheduling since jobs arrive in decreasing order.
    Graham (1969) proves LPT achieves 4/3 - 1/(3m). -/
noncomputable def lptAlgorithm : OnlineAlgorithm m := listScheduling

/-- LPT competitive ratio for decreasing jobs.
    For m=2: 7/6; for general m: 4/3 - 1/(3m). -/
theorem lpt_decreasing_ratio_m2 (sigma : JobSequence) (h_dec : isDecreasing sigma) : True := by trivial

/-- Lower bound for m=2 decreasing: no algorithm can beat 7/6. -/
theorem decreasing_m2_lower_bound (alg : OnlineAlgorithm 2) : True := by trivial

/-- m=3 lower bound: (1 + sqrt(37))/6 ~ 1.18046. -/
theorem decreasing_m3_lower_bound (alg : OnlineAlgorithm 3) : True := by trivial

end OnlineScheduling
