/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Adaptive Adversary Trees: the certification layer for automatic lower bounds

This is the one-time soundness backbone of the "LLM generates template →
numerical optimization → Lean certification" pipeline: an *adversary tree*
spells out an adaptive adversary explicitly —

- every internal node stores a concrete state `(σ, loads)` and releases one job `p`;
- the deterministic online algorithm answers with a machine `i : Fin m`, and the
  tree follows the child `children i`;
- a stop leaf carries the witness sequence `σ` together with the load vector
  `loads` reached along the path.

`sound` proves **once, for every m**: if the tree is well-formed (children store
exactly the states the adversary expects), rooted at the empty state, and every
stop leaf is *certified* (`ρ·OPT(σ) − d ≤ makespan(loads)`), then every
deterministic online algorithm admits a witness sequence with
`τ_A(σ) ≥ ρ·τ_o(σ) − d`.

Hence a template instance is **pure data**: enumerate placements, attach per-leaf
certificates (assignment packings + norm_num/decide arithmetic). No new
mathematical proof is needed per template.
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

noncomputable section

variable (m : ℕ) [NeZero m]

/-- An adaptive adversary tree over `m` machines. `stop σ loads` is a witness
    leaf; `node σ loads p children` releases job `p` from the concrete state
    `(σ, loads)` and branches on the machine the algorithm chooses. -/
inductive AdvTree where
  | stop (σ : JobSequence) (loads : Loads m)
  | node (σ : JobSequence) (loads : Loads m) (p : Job) (children : Fin m → AdvTree)

namespace AdvTree

variable {m}

/-- The witness sequence stored at a tree node. -/
def sigma : AdvTree m → JobSequence
  | .stop σ _ => σ
  | .node σ _ _ _ => σ

/-- The load vector stored at a tree node. -/
def loads : AdvTree m → Loads m
  | .stop _ l => l
  | .node _ l _ _ => l

/-- The state reached when job `p` is placed on machine `i`. -/
def place (loads : Loads m) (p : Job) (i : Fin m) : Loads m :=
  fun j => if j = i then loads j + p else loads j

/-- Well-formed: every child stores the sequence extended by `p` and the load
    vector obtained by placing `p` on the chosen machine, recursively. -/
def WellFormed : AdvTree m → Prop
  | .stop _ _ => True
  | .node σ loads p children =>
      (∀ i, WellFormed (children i)) ∧
      (∀ i, (children i).sigma = σ ++ [p]) ∧
      (∀ i, (children i).loads = place (m := m) loads p i)

/-- Certified: every stop leaf proves the target additive bound at its
    witness: `ρ·OPT(σ) − d ≤ makespan(loads)`. -/
def Certified (ρ d : ℝ) : AdvTree m → Prop
  | .stop σ loads => ρ * optMakespan (m := m) σ - d ≤ makespan m loads
  | .node _ _ _ children => ∀ i, Certified ρ d (children i)

/-- The witness sequence an algorithm produces by following the tree. -/
def play (alg : OnlineAlgorithm m) : AdvTree m → JobSequence
  | .stop σ _ => σ
  | .node _ loads p children => play alg (children (alg loads p))

/-- Root convention: the tree starts from the empty sequence and zero loads. -/
def rootOK (T : AdvTree m) : Prop := T.sigma = [] ∧ T.loads = fun _ => 0

/-- Stop leaf smart constructor (always well-formed). -/
def mkStop (σ : JobSequence) (loads : Loads m) : { T : AdvTree m // T.WellFormed } :=
  ⟨.stop σ loads, by trivial⟩

/-- Node smart constructor carrying the well-formedness proof. -/
def mkNode (σ : JobSequence) (loads : Loads m) (p : Job)
    (children : Fin m → { T : AdvTree m // T.WellFormed })
    (h : ∀ i, (children i).1.sigma = σ ++ [p] ∧ (children i).1.loads = place (m := m) loads p i) :
    { T : AdvTree m // T.WellFormed } :=
  ⟨.node σ loads p (fun i => (children i).1), by
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact (children i).2
    · intro i; exact (h i).1
    · intro i; exact (h i).2⟩

private theorem sound_aux (alg : OnlineAlgorithm m) (T : AdvTree m) (ρ d : ℝ) :
    T.WellFormed → T.loads = runAlgorithm m alg T.sigma → T.Certified ρ d →
    ∃ σ : JobSequence, ρ * optMakespan (m := m) σ - d ≤ algorithmMakespan m alg σ := by
  induction T with
  | stop σ loads =>
      intro hwf hloads hcert
      refine ⟨σ, ?_⟩
      dsimp [algorithmMakespan, AdvTree.sigma, AdvTree.loads] at hloads ⊢
      rw [← hloads]
      exact hcert
  | node σ loads p children ih =>
      intro hwf hloads hcert
      rcases hwf with ⟨hwf_ch, hσ_ch, hl_ch⟩
      dsimp [AdvTree.sigma, AdvTree.loads] at hloads
      have hchild : (children (alg loads p)).loads =
          runAlgorithm m alg (children (alg loads p)).sigma := by
        rw [hσ_ch (alg loads p), runAlgorithm_append_singleton (m := m) alg σ p]
        rw [← hloads]
        rw [hl_ch (alg loads p)]
        rfl
      exact ih (alg loads p) (hwf_ch (alg loads p)) hchild (hcert (alg loads p))

/-- **Soundness of the certified adversary tree** (proved once, for every m):
    a well-formed tree rooted at the empty state whose stop leaves are all
    certified for `ρ, d` forces every deterministic online algorithm to admit
    a witness sequence with `ρ·OPT(σ) − d ≤ τ_A(σ)`. -/
theorem sound (T : AdvTree m) (hT : T.WellFormed) (hroot : T.rootOK) (ρ d : ℝ)
    (hcert : T.Certified ρ d) :
    ∀ alg : OnlineAlgorithm m, ∃ σ : JobSequence,
      ρ * optMakespan (m := m) σ - d ≤ algorithmMakespan m alg σ := by
  intro alg
  have hloads0 : T.loads = runAlgorithm m alg T.sigma := by
    rcases hroot with ⟨hσ, hl⟩
    rw [hσ, hl]
    rfl
  exact sound_aux alg T ρ d hT hloads0 hcert

end AdvTree

end

end OnlineScheduling
