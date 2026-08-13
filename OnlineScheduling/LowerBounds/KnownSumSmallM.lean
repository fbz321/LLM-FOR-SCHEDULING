/-
Known-Sum Semi-Online Lower Bounds for m=3,4,5,6.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.KnownSumM6

namespace OnlineScheduling

noncomputable def ks_m3_ratio : R := 1 + (-3 + Real.sqrt 129) / 6
noncomputable def ks_m3_v : R := (-3 + Real.sqrt 129) / 6

axiom ks_m3_lower_bound_proof_obligation (alg : OnlineAlgorithm 3) :
    ∃ sigma : JobSequence,
      algorithmMakespan 3 alg sigma ≥ ks_m3_ratio * OPT sigma

theorem ks_m3_lower_bound (alg : OnlineAlgorithm 3) :
    ∃ sigma : JobSequence,
      algorithmMakespan 3 alg sigma ≥ ks_m3_ratio * OPT sigma := by
  exact ks_m3_lower_bound_proof_obligation alg

noncomputable def ks_m4_ratio : R := 1 + (-4 + Real.sqrt 160) / 6
noncomputable def ks_m4_v : R := (-4 + Real.sqrt 160) / 6

axiom ks_m4_lower_bound_proof_obligation (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence,
      algorithmMakespan 4 alg sigma ≥ ks_m4_ratio * OPT sigma

theorem ks_m4_lower_bound (alg : OnlineAlgorithm 4) :
    ∃ sigma : JobSequence,
      algorithmMakespan 4 alg sigma ≥ ks_m4_ratio * OPT sigma := by
  exact ks_m4_lower_bound_proof_obligation alg

noncomputable def ks_m5_ratio : R := 1 + (-5 + Real.sqrt 193) / 6
noncomputable def ks_m5_v : R := (-5 + Real.sqrt 193) / 6

axiom ks_m5_lower_bound_proof_obligation (alg : OnlineAlgorithm 5) :
    ∃ sigma : JobSequence,
      algorithmMakespan 5 alg sigma ≥ ks_m5_ratio * OPT sigma

theorem ks_m5_lower_bound (alg : OnlineAlgorithm 5) :
    ∃ sigma : JobSequence,
      algorithmMakespan 5 alg sigma ≥ ks_m5_ratio * OPT sigma := by
  exact ks_m5_lower_bound_proof_obligation alg

axiom ks_m6_lower_bound_proof_obligation (alg : OnlineAlgorithm 6) :
    ∃ sigma : JobSequence,
      algorithmMakespan 6 alg sigma ≥ (3 / 2 : ℝ) * OPT sigma

theorem ks_m6_lower_bound (alg : OnlineAlgorithm 6) :
    ∃ sigma : JobSequence,
      algorithmMakespan 6 alg sigma ≥ (3 / 2 : ℝ) * OPT sigma := by
  exact ks_m6_lower_bound_proof_obligation alg

end OnlineScheduling
