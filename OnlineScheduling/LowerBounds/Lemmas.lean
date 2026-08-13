/-
Minimal lemma stubs for bottleneck reflection.
Replace axomi with real proofs from Faigle.lean when mathlib is updated.
-/
import OnlineScheduling.Basic

namespace OnlineScheduling

/-! ### OPT of m identical jobs -/

axiom opt_of_identical_jobs {m : ℕ} [NeZero m] (x : ℝ) (hxpos : 0 < x) :
    OPT (List.replicate m x) = x

/-! ### Layer separation: either ratio ≥ 2 or perfectly balanced -/

axiom layer_separation {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m) (x : ℝ) (hxpos : 0 < x) :
    let σ := List.replicate m x
    algorithmMakespan m alg σ ≥ 2 * OPT σ
    ∨ (∀ i : Fin m, runAlgorithm m alg σ i = x)

/-! ### Layer separation from a uniform base load -/

axiom layer_separation_from_base {m : ℕ} [NeZero m] (alg : OnlineAlgorithm m)
    (base x : ℝ) (hxpos : 0 < x)
    (loads_before : Loads m) (h_uniform : ∀ i : Fin m, loads_before i = base) :
    let tau := List.replicate m x
    let loads_after := tau.foldl (step (m := m) alg) loads_before
    makespan m loads_after ≥ base + 2 * x
    ∨ (∀ i : Fin m, loads_after i = base + x)

end OnlineScheduling
