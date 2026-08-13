import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Lemmas
open OnlineScheduling

set_option maxHeartbeats 400000

theorem lower_bound_{{TARGET_SHORT}} {m : ℕ} [NeZero m] (hm : 4 ≤ m) (alg : OnlineAlgorithm m) :
    ∃ (σ : JobSequence), algorithmMakespan m alg σ ≥ ({{TARGET}} : ℝ) * OPT σ :=
by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (m : ℝ) ≠ 0 := by
    have hpos : 0 < (m : ℕ) := Nat.pos_of_neZero (n := m)
    exact_mod_cast hpos.ne.symm
  set a₁ := {{A1}} with ha₁_def
  set a₂ := {{A2}} with ha₂_def
  {{A3_LINE}}
  set F := {{F}} with hF_def
  have ha₁pos : 0 < a₁ := by norm_num [ha₁_def]
  have ha₂pos : 0 < a₂ := by norm_num [ha₂_def]
  {{A3POS_LINE}}
  have hFpos : 0 < F := by norm_num [hF_def]
  set σ₁ := List.replicate m a₁ with hσ₁_def
  have h_p1 := layer_separation (m := m) alg a₁ ha₁pos
  rcases h_p1 with (h_imbal1 | h_bal1)
  · use σ₁
    have h_opt : OPT σ₁ = a₁ := opt_of_identical_jobs (m := m) a₁ ha₁pos
    nlinarith
  · have h_loads1 : ∀ i : Fin m, runAlgorithm m alg σ₁ i = a₁ := h_bal1
    let loads₁ := runAlgorithm m alg σ₁
    let τ₂ := List.replicate m a₂
    set σ₂ := σ₁ ++ τ₂ with hσ₂_def
    have h_p2 := layer_separation_from_base (m := m) alg a₁ a₂ ha₂pos loads₁ h_loads1
    rcases h_p2 with (h_imbal2 | h_bal2)
    · use σ₂
      have h_sched : totalLoad σ₂ = ∑ i : Fin m, (λ _ : Fin m => a₁ + a₂) i := by
        dsimp [σ₂, σ₁, τ₂, totalLoad]; simp [hσ₁_def]; ring
      have h_opt : OPT σ₂ ≤ a₁ + a₂ :=
        opt_le_of_schedule (m := m) σ₂ (λ _ => a₁ + a₂) h_sched
      rw [ha₁_def, ha₂_def]
      norm_num
      nlinarith
    · have h_loads2 : ∀ i : Fin m, (τ₂.foldl (step (m := m) alg) loads₁) i = a₁ + a₂ := h_bal2
      set loads₂ := τ₂.foldl (step (m := m) alg) loads₁ with h_loads₂_def
      {{PHASE3_BLOCK}}
      set σ_final := {{FINAL_SIGMA}} with hσ_final_def
      use σ_final
      have h_sched : totalLoad σ_final = ∑ i : Fin m, (λ _ : Fin m => {{OPT_BOUND}}) i := by
        dsimp [σ_final, {{ALL_SIGMAS}}, totalLoad]; simp [hσ₁_def]; ring
      have h_opt : OPT σ_final ≤ {{OPT_BOUND}} :=
        opt_le_of_schedule (m := m) σ_final (λ _ => {{OPT_BOUND}}) h_sched
      have h_mk : {{MK_BOUND}} ≤ algorithmMakespan m alg σ_final := by
        have h := makespan_ge_each (m := m) (runAlgorithm m alg σ_final)
          (alg loads₂ F)
        have hload : runAlgorithm m alg σ_final (alg loads₂ F) =
          loads₂ (alg loads₂ F) + F := by
          rw [hσ_final_def, runAlgorithm_append_singleton alg {{PREV_SIGMA}} F,
            show runAlgorithm m alg {{PREV_SIGMA}} = loads₂ from rfl]
          dsimp [step]; simp
        rw [hload, h_loads₂_def]
        have hh : loads₂ (alg loads₂ F) = a₁ + a₂ := h_loads2 (alg loads₂ F)
        rw [hh] at h
        nlinarith
      have hm4_inv : (1 : ℝ)/4 ≤ 1/(m : ℝ) := by
        refine (one_div_le_one_div ?_ ?_).mpr hm4
        · norm_num; · have hpos : 0 < (m : ℕ) := Nat.pos_of_neZero (n := m); exact_mod_cast hpos
      rw [{{REWRITES}}]
      nlinarith
