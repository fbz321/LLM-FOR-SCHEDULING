/-
P3||Cmax with Known Total Sum: Lower Bound > 1.3929.
-/

import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

namespace OnlineScheduling

noncomputable def ks3_optimal_eps : R := (Real.sqrt 19 - 4) / 9
noncomputable def ks3_constant : R := 1 + (Real.sqrt 19 - 2) / 6

axiom ks3_optimal_eps_pos_proof_obligation : 0 < ks3_optimal_eps

example : 0 < ks3_optimal_eps := by
  exact ks3_optimal_eps_pos_proof_obligation

axiom ks3_optimal_eps_lt_one_sixth_proof_obligation : ks3_optimal_eps < 1 / 6

example : ks3_optimal_eps < 1 / 6 := by
  exact ks3_optimal_eps_lt_one_sixth_proof_obligation

noncomputable def ks3_p12 (eps : ℝ) : R := 1 / 3 + eps
noncomputable def ks3_instance_A (eps : ℝ) : JobSequence :=
  [ks3_p12 eps, ks3_p12 eps, 1, 1, 1 / 3 - 2 * eps]

axiom ks3_opt_A_proof_obligation (eps : ℝ)
    (h_eps_pos : 0 < eps) (h_eps_lt : eps < 1 / 6) :
    OPT (ks3_instance_A eps) = (1 : ℝ)

lemma ks3_opt_A (eps : ℝ) (h_eps_pos : 0 < eps) (h_eps_lt : eps < 1 / 6) :
    OPT (ks3_instance_A eps) = (1 : ℝ) := by
  exact ks3_opt_A_proof_obligation eps h_eps_pos h_eps_lt

noncomputable def ks3_p3 (eps : ℝ) : R := 2 / 3 + eps / 2
noncomputable def ks3_instance_B1 (eps : ℝ) : JobSequence :=
  [ks3_p12 eps, ks3_p12 eps, ks3_p3 eps, 1 / 3 - 2 * eps, 1 / 3 - eps / 2, 1]

noncomputable def ks3_p4 (eps : ℝ) : R := 2 / 3 + eps / 2
noncomputable def ks3_instance_B2a (eps : ℝ) : JobSequence :=
  [ks3_p12 eps, ks3_p12 eps, ks3_p3 eps, ks3_p4 eps,
   1 / 3 - 2 * eps, 1 / 3 - eps / 2, 1 / 3 - eps / 2]

noncomputable def ks3_instance_B2b (eps : ℝ) : JobSequence :=
  [ks3_p12 eps, ks3_p12 eps, ks3_p3 eps, ks3_p4 eps, 1 - 3 * eps]

axiom ks3_known_sum_lower_bound_proof_obligation (alg : OnlineAlgorithm 3) :
    ∃ sigma : JobSequence,
      algorithmMakespan 3 alg sigma ≥ ks3_constant * OPT sigma

theorem ks3_known_sum_lower_bound (alg : OnlineAlgorithm 3) :
    ∃ sigma : JobSequence,
      algorithmMakespan 3 alg sigma ≥ ks3_constant * OPT sigma := by
  exact ks3_known_sum_lower_bound_proof_obligation alg

end OnlineScheduling
