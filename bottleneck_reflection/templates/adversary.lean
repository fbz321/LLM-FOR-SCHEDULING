import OnlineScheduling.Basic
import OnlineScheduling.LowerBounds.Faigle

open OnlineScheduling
open Finset

set_option maxHeartbeats 400000

/--
Prove the deterministic competitive ratio lower bound for P|online,list|Cmax
is at least {{TARGET}}.

This improves upon the best known lower bound of 1.880 (Rudin 2003).

Strategy: layered adversary construction.
{{STRATEGY_DESCRIPTION}}
-/

theorem improved_lower_bound_{{TARGET_SHORT}} {m : ℕ} [NeZero m]
    (hm : 4 ≤ m) (alg : OnlineAlgorithm m) :
    ∃ (σ : JobSequence),
    algorithmMakespan m alg σ ≥ ({{TARGET}} : ℝ) * OPT σ :=
by
  have hm_rat : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos_rat : (m : ℝ) ≠ 0 := by
    have hpos : 0 < (m : ℕ) := Nat.pos_of_neZero
    exact_mod_cast hpos.ne.symm

  -- TODO: Define job sizes and prove the bound
  -- Use `set ... := ... with ..._def` for all named values
  -- Use `nlinarith` and `field_simp` for algebraic proofs
  -- Use `opt_of_identical_jobs`, `opt_le_of_schedule` for OPT bounds
  -- Use `layer_separation` and `layer_separation_from_base` for adversary branching

  sorry
