/-
Copyright (c) 2026 OnlineScheduling contributors. All rights reserved.
Released under Apache 2.0 license.

# Braun–Chung–Graham 2025 r=0: replay through the certification layer

This file is the *smoke test* of the template-data model: the r = 0 Braun
adversary (9 jobs: L₀×4, S₀×4, F) is spelled out as an explicit `AdvTree` —
every placement branch is enumerated, every stop leaf carries a mechanical
certificate (the proven layer-separation lemma plus assignment packings) —
and `braun_tree_lower_bound` re-derives Theorem 1's instance purely through
`AdvTree.sound`. No new mathematical proof is written here.
-/

import OnlineScheduling.LowerBounds.AdversaryTree
import OnlineScheduling.LowerBounds.BraunGraham2025

namespace OnlineScheduling

noncomputable section

namespace BraunTree

open AdvTree

/-- Place four identical jobs of size `x` on machines `m1 m2 m3 m4` in order. -/
def place4 (loads : Loads 4) (x : ℝ) (m1 m2 m3 m4 : Fin 4) : Loads 4 :=
  place (m := 4) (place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3) x m4

/-- Release four identical jobs `x` from state `(σ, loads)` and hand the
    resulting state to `leaf`. -/
def stage4 (σ : JobSequence) (loads : Loads 4) (x : ℝ)
    (leaf : JobSequence → Loads 4 → AdvTree 4) : AdvTree 4 :=
  .node σ loads x (fun m1 =>
    .node (σ ++ [x]) (place (m := 4) loads x m1) x (fun m2 =>
      .node (σ ++ [x, x]) (place (m := 4) (place (m := 4) loads x m1) x m2) x (fun m3 =>
        .node (σ ++ [x, x, x]) (place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3) x (fun m4 =>
          leaf (σ ++ [x, x, x, x]) (place4 loads x m1 m2 m3 m4)))))

/-- Release one job `x` from state `(σ, loads)` and hand the resulting state
    to `leaf`. -/
def stage1 (σ : JobSequence) (loads : Loads 4) (x : ℝ)
    (leaf : JobSequence → Loads 4 → AdvTree 4) : AdvTree 4 :=
  .node σ loads x (fun m => leaf (σ ++ [x]) (place (m := 4) loads x m))

/-- The F stage: every placement stops immediately. -/
def fLeaf (σ : JobSequence) (loads : Loads 4) : AdvTree 4 :=
  .stop σ loads

/-- The S₀ stage classifier: balanced continuation or stop. -/
def s0Leaf (σ : JobSequence) (loads : Loads 4) : AdvTree 4 :=
  if _ : ∀ i : Fin 4, loads i = braunL 0 + braunS 0 then
    stage1 σ loads (braunF 0) fLeaf
  else
    .stop σ loads

/-- The L₀ stage classifier: balanced continuation or stop. -/
def l0Leaf (σ : JobSequence) (loads : Loads 4) : AdvTree 4 :=
  if _ : ∀ i : Fin 4, loads i = braunL 0 then
    stage4 σ loads (braunS 0) s0Leaf
  else
    .stop σ loads

/-- The Braun r = 0 adversary as an explicit tree. -/
def braunTree : AdvTree 4 :=
  stage4 [] (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) l0Leaf

/-- The online algorithm whose next moves are the tuple m1..m4, identified by
    the running total load: base, base+step, base+2·step, otherwise. -/
def tupleAlg4 (base step : ℝ) (m1 m2 m3 m4 : Fin 4) : OnlineAlgorithm 4 :=
  fun loads _ =>
    if (∑ i : Fin 4, loads i) = base then m1
    else if (∑ i : Fin 4, loads i) = base + step then m2
    else if (∑ i : Fin 4, loads i) = base + 2 * step then m3
    else m4

/-- Placing one job increases the total load by the job size. -/
lemma sum_place (loads : Loads 4) (x : ℝ) (m : Fin 4) :
    (∑ i : Fin 4, place (m := 4) loads x m i) = (∑ i : Fin 4, loads i) + x := by
  calc
    (∑ i : Fin 4, place (m := 4) loads x m i)
        = ∑ i : Fin 4, (loads i + (if i = m then x else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = m <;> simp [place, h]
    _ = (∑ i : Fin 4, loads i) + x := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp

/-- The total load after four placements grows by 4·x. -/
lemma sum_place4 (loads : Loads 4) (x : ℝ) (m1 m2 m3 m4 : Fin 4) :
    (∑ i : Fin 4, place4 loads x m1 m2 m3 m4 i) = (∑ i : Fin 4, loads i) + 4 * x := by
  dsimp [place4]
  rw [sum_place, sum_place, sum_place, sum_place]
  ring

/-- Releasing four jobs through the tuple algorithm reproduces the tuple
    placements (when the initial total is `base` and the step is nonzero). -/
lemma tupleAlg4_run (base x : ℝ) (hx : x ≠ 0) (loads : Loads 4)
    (hsum : (∑ i : Fin 4, loads i) = base) (m1 m2 m3 m4 : Fin 4) :
    place4 loads x m1 m2 m3 m4 =
      (List.replicate 4 x).foldl (step (m := 4) (tupleAlg4 base x m1 m2 m3 m4)) loads := by
  dsimp [place4]
  have h1 : tupleAlg4 base x m1 m2 m3 m4 loads x = m1 := by
    dsimp [tupleAlg4]
    rw [if_pos hsum]
  have hstep1 : step (m := 4) (tupleAlg4 base x m1 m2 m3 m4) loads x = place (m := 4) loads x m1 := by
    dsimp [step]
    rw [h1]
    rfl
  rw [hstep1]
  have hsum1 : (∑ i : Fin 4, place (m := 4) loads x m1 i) = base + x := by
    rw [sum_place, hsum]
  have h2ne1 : (∑ i : Fin 4, place (m := 4) loads x m1 i) ≠ base := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum1]
    exact hx hx0
  have h2 : tupleAlg4 base x m1 m2 m3 m4 (place (m := 4) loads x m1) x = m2 := by
    dsimp [tupleAlg4]
    rw [if_neg h2ne1, if_pos hsum1]
  have hstep2 : step (m := 4) (tupleAlg4 base x m1 m2 m3 m4) (place (m := 4) loads x m1) x =
      place (m := 4) (place (m := 4) loads x m1) x m2 := by
    dsimp [step]
    rw [h2]
    rfl
  rw [hstep2]
  have hsum2 : (∑ i : Fin 4, place (m := 4) (place (m := 4) loads x m1) x m2 i) = base + 2 * x := by
    rw [sum_place, sum_place, hsum]
    ring
  have h3ne1 : (∑ i : Fin 4, place (m := 4) (place (m := 4) loads x m1) x m2 i) ≠ base := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum2]
    exact hx hx0
  have h3ne2 : (∑ i : Fin 4, place (m := 4) (place (m := 4) loads x m1) x m2 i) ≠ base + x := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum2]
    exact hx hx0
  have h3 : tupleAlg4 base x m1 m2 m3 m4 (place (m := 4) (place (m := 4) loads x m1) x m2) x = m3 := by
    dsimp [tupleAlg4]
    rw [if_neg h3ne1, if_neg h3ne2, if_pos hsum2]
  have hstep3 : step (m := 4) (tupleAlg4 base x m1 m2 m3 m4) (place (m := 4) (place (m := 4) loads x m1) x m2) x =
      place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3 := by
    dsimp [step]
    rw [h3]
    rfl
  rw [hstep3]
  have hsum3 : (∑ i : Fin 4, place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3 i) = base + 3 * x := by
    rw [sum_place, sum_place, sum_place, hsum]
    ring
  have h4ne1 : (∑ i : Fin 4, place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3 i) ≠ base := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum3]
    exact hx hx0
  have h4ne2 : (∑ i : Fin 4, place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3 i) ≠ base + x := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum3]
    exact hx hx0
  have h4ne3 : (∑ i : Fin 4, place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3 i) ≠ base + 2 * x := by
    intro h
    have hx0 : x = 0 := by linarith [h, hsum3]
    exact hx hx0
  have h4 : tupleAlg4 base x m1 m2 m3 m4 (place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3) x = m4 := by
    dsimp [tupleAlg4]
    rw [if_neg h4ne1, if_neg h4ne2, if_neg h4ne3]
  have hstep4 : step (m := 4) (tupleAlg4 base x m1 m2 m3 m4) (place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3) x =
      place (m := 4) (place (m := 4) (place (m := 4) (place (m := 4) loads x m1) x m2) x m3) x m4 := by
    dsimp [step]
    rw [h4]
    rfl
  rw [hstep4]

/-- L₀ trap certificate: unless the four L₀ jobs are perfectly balanced, the
    makespan reaches 2·L₀ (layer separation). -/
lemma l0bad (m1 m2 m3 m4 : Fin 4)
    (h : ¬ ∀ i : Fin 4, place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4 i = braunL 0) :
    2 * braunL 0 ≤ makespan 4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) := by
  let alg : OnlineAlgorithm 4 := tupleAlg4 0 (braunL 0) m1 m2 m3 m4
  have hsum0 : (∑ i : Fin 4, (fun _ : Fin 4 => (0 : ℝ)) i) = (0 : ℝ) := by simp
  have hrun := tupleAlg4_run 0 (braunL 0) (by dsimp [braunL]; norm_num) (fun _ : Fin 4 => (0 : ℝ)) hsum0 m1 m2 m3 m4
  rcases braun_layer_separation_from_base alg 0 (braunL 0) (braunL_pos 0)
      (fun _ : Fin 4 => (0 : ℝ)) (by intro i; rfl) with hbad | hgood
  · rw [← hrun] at hbad
    simpa using hbad
  · exfalso
    apply h
    intro i
    rw [hrun]
    simpa using hgood i

/-- S₀ trap certificate: on top of a balanced L₀ layer, two S₀ jobs on one
    machine reach L₀ + 2·S₀ (layer separation). -/
lemma s0bad (loads : Loads 4) (hloads : ∀ i : Fin 4, loads i = braunL 0)
    (m1 m2 m3 m4 : Fin 4)
    (h : ¬ ∀ i : Fin 4, place4 loads (braunS 0) m1 m2 m3 m4 i = braunL 0 + braunS 0) :
    braunL 0 + 2 * braunS 0 ≤ makespan 4 (place4 loads (braunS 0) m1 m2 m3 m4) := by
  let alg : OnlineAlgorithm 4 := tupleAlg4 (4 * braunL 0) (braunS 0) m1 m2 m3 m4
  have hsum : (∑ i : Fin 4, loads i) = 4 * braunL 0 := by
    simp [hloads, Finset.sum_const]
  have hrun := tupleAlg4_run (4 * braunL 0) (braunS 0) (by
      dsimp [braunS, braunL]
      nlinarith [braunα_pos]) loads hsum m1 m2 m3 m4
  rcases braun_layer_separation_from_base alg (braunL 0) (braunS 0) (braunS_pos 0) loads hloads with hbad | hgood
  · rw [← hrun] at hbad
    simpa using hbad
  · exfalso
    apply h
    intro i
    rw [hrun]
    simpa using hgood i

/-- F finish certificate: from the balanced S₀ state, the final job forces the
    exact additive bound. -/
lemma fgood (loads : Loads 4) (hloads : ∀ i : Fin 4, loads i = braunL 0 + braunS 0) (m : Fin 4) :
    braunSumLS 0 + braunF 0 ≤ makespan 4 (place (m := 4) loads (braunF 0) m) := by
  have hm : braunSumLS 0 + braunF 0 ≤ place (m := 4) loads (braunF 0) m m := by
    dsimp [place]
    rw [if_pos rfl]
    rw [hloads m]
    simp [braunSumLS]
  exact le_trans hm (makespan_ge_each (m := 4) (place (m := 4) loads (braunF 0) m) m)

/-- The Braun r = 0 tree is well-formed. -/
lemma braunTree_wellFormed : WellFormed braunTree := by
  dsimp [braunTree]
  refine ⟨?_, ?_, ?_⟩
  · intro m1; refine ⟨?_, ?_, ?_⟩
    · intro m2; refine ⟨?_, ?_, ?_⟩
      · intro m3; refine ⟨?_, ?_, ?_⟩
        · intro m4
          dsimp [l0Leaf]
          by_cases h : ∀ i : Fin 4, place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4 i = braunL 0
          · simp [h]
            refine ⟨?_, ?_, ?_⟩
            · intro m1'; refine ⟨?_, ?_, ?_⟩
              · intro m2'; refine ⟨?_, ?_, ?_⟩
                · intro m3'; refine ⟨?_, ?_, ?_⟩
                  · intro m4'
                    dsimp [s0Leaf]
                    by_cases h' : ∀ i : Fin 4, place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4' i = braunL 0 + braunS 0
                    · simp [h']
                      dsimp [stage1, fLeaf]
                      refine ⟨?_, ?_, ?_⟩
                      · intro m; simp [WellFormed]
                      · intro m; rfl
                      · intro m; rfl
                    · simp [h', WellFormed]
                  · intro m4'
                    by_cases h' : ∀ i : Fin 4, place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4' i = braunL 0 + braunS 0 <;>
                      simp [s0Leaf, stage1, AdvTree.sigma, h']
                  · intro m4'
                    by_cases h' : ∀ i : Fin 4, place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4' i = braunL 0 + braunS 0 <;>
                      simp [s0Leaf, stage1, AdvTree.loads, h'] <;> rfl
                · intro m3'; rfl
                · intro m3'; rfl
              · intro m2'; rfl
              · intro m2'; rfl
            · intro m1'; rfl
            · intro m1'; rfl
          · simp [h, WellFormed]
        · intro m4
          by_cases h : ∀ i : Fin 4, place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4 i = braunL 0 <;>
            simp [l0Leaf, stage4, AdvTree.sigma, h]
        · intro m4
          by_cases h : ∀ i : Fin 4, place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4 i = braunL 0 <;>
            simp [l0Leaf, stage4, AdvTree.loads, h] <;> rfl
      · intro m3; rfl
      · intro m3; rfl
    · intro m2; rfl
    · intro m2; rfl
  · intro m1; rfl
  · intro m1; rfl

/-- Every stop leaf of the Braun r = 0 tree carries the certificate
    `√3·OPT − (2−√3) ≤ makespan`. -/
lemma braunTree_certified : Certified (Real.sqrt 3) (2 - Real.sqrt 3) braunTree := by
  dsimp [braunTree, Certified]
  intro m1 m2 m3 m4
  dsimp [l0Leaf]
  by_cases h : ∀ i : Fin 4, place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4 i = braunL 0
  · simp [h]
    dsimp [stage4, Certified]
    intro m1' m2' m3' m4'
    dsimp [s0Leaf]
    by_cases h' : ∀ i : Fin 4, place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4' i = braunL 0 + braunS 0
    · simp [h']
      dsimp [stage1, fLeaf, Certified]
      intro m
      calc
        Real.sqrt 3 * optMakespan (m := 4) ((([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
              [braunS 0, braunS 0, braunS 0, braunS 0]) ++ [braunF 0]) - (2 - Real.sqrt 3)
            = Real.sqrt 3 * braunF 0 - (2 - Real.sqrt 3) := by
              have hopt : optMakespan (m := 4) ((([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
                  [braunS 0, braunS 0, braunS 0, braunS 0]) ++ [braunF 0]) = braunF 0 := by
                rw [show ((([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
                    [braunS 0, braunS 0, braunS 0, braunS 0]) ++ [braunF 0]) = braunSeq 0 by rfl]
                exact braun_opt_eq_F 0
              rw [hopt]
        _ = braunForcedMakespan 0 := by
              rw [braun_additive_identity 0]
        _ = braunSumLS 0 + braunF 0 := by rfl
        _ ≤ makespan 4 (place (m := 4) (place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4') (braunF 0) m) := by
              exact fgood (place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4') h' m
    · simp [h']
      dsimp [Certified]
      calc
        Real.sqrt 3 * optMakespan (m := 4) (([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
              [braunS 0, braunS 0, braunS 0, braunS 0]) - (2 - Real.sqrt 3)
            = Real.sqrt 3 * (braunL 0 + braunS 0) - (2 - Real.sqrt 3) := by
              have hopt : optMakespan (m := 4) (([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
                  [braunS 0, braunS 0, braunS 0, braunS 0]) = braunL 0 + braunS 0 := by
                rw [show ([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) ++
                    [braunS 0, braunS 0, braunS 0, braunS 0] = braunPrefixSp 0 by rfl]
                exact braun_opt_prefix0
              rw [hopt]
        _ ≤ braunL 0 + 2 * braunS 0 := braun_trap_S0
        _ ≤ makespan 4 (place4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) (braunS 0) m1' m2' m3' m4') := by
              exact s0bad (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) h m1' m2' m3' m4' h'
  · simp [h]
    dsimp [Certified]
    calc
      Real.sqrt 3 * optMakespan (m := 4) ([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) - (2 - Real.sqrt 3)
          = Real.sqrt 3 * braunL 0 - (2 - Real.sqrt 3) := by
            have hopt : optMakespan (m := 4) ([] ++ [braunL 0, braunL 0, braunL 0, braunL 0]) = braunL 0 := by
              rw [show [] ++ [braunL 0, braunL 0, braunL 0, braunL 0] = List.replicate 4 (braunL 0) by rfl]
              exact braun_opt_replicate4_L0
            rw [hopt]
      _ ≤ 2 * braunL 0 := braun_trap_L0
      _ ≤ makespan 4 (place4 (fun _ : Fin 4 => (0 : ℝ)) (braunL 0) m1 m2 m3 m4) := by
            exact l0bad m1 m2 m3 m4 h

/-- The Braun r = 0 tree is rooted at the empty state. -/
lemma braunTree_rootOK : rootOK braunTree := by
  dsimp [braunTree, rootOK, AdvTree.sigma, AdvTree.loads]
  constructor <;> rfl

/-- Braun–Chung–Graham 2025, r = 0 instance, derived purely through the
    certification layer: every deterministic online algorithm on 4 machines
    admits a sequence with makespan ≥ √3·OPT − (2−√3). -/
theorem braun_tree_lower_bound (alg : OnlineAlgorithm 4) :
    ∃ σ : JobSequence,
      Real.sqrt 3 * optMakespan (m := 4) σ - (2 - Real.sqrt 3) ≤ algorithmMakespan 4 alg σ :=
  AdvTree.sound braunTree braunTree_wellFormed braunTree_rootOK (Real.sqrt 3) (2 - Real.sqrt 3)
    braunTree_certified alg

end BraunTree

end

end OnlineScheduling
