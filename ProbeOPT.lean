/- Probe: does the current OPT axiom set collapse OPT to the average load? -/
import OnlineScheduling.Basic

namespace OnlineScheduling

noncomputable section

/-- OPT ≤ average load, derivable from opt_le_of_schedule with the constant vector. -/
lemma probe_opt_le_avg (σ : JobSequence) : OPT σ ≤ totalLoad σ / 4 := by
  have h := opt_le_of_schedule (m := 4) σ (λ _ : Fin 4 => totalLoad σ / 4) (by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring)
  have hm : makespan 4 (λ _ : Fin 4 => totalLoad σ / 4) = totalLoad σ / 4 :=
    makespan_const 4 (totalLoad σ / 4)
  rwa [hm] at h

/-- Hence OPT = average load for every sequence (with m = 4). -/
lemma probe_opt_eq_avg (σ : JobSequence) : OPT σ = totalLoad σ / 4 := by
  apply le_antisymm
  · exact probe_opt_le_avg σ
  · exact opt_ge_avg_load (m := 4) σ

/-- The axiom set is inconsistent: σ = [1] gives 1 ≤ OPT [1] = 1/4. -/
lemma probe_contradiction : False := by
  have hmax : maxJobSize ([1] : JobSequence) = 1 := by
    dsimp [maxJobSize]; norm_num
  have hge : (1 : ℝ) ≤ OPT ([1] : JobSequence) := by
    rw [← hmax]; exact opt_ge_max_job _
  have heq : OPT ([1] : JobSequence) = 1 / 4 := by
    rw [probe_opt_eq_avg]
    dsimp [totalLoad]; norm_num
  linarith [hge, heq]

end