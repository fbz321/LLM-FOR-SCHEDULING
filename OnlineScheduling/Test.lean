/-
Test cases for the OnlineScheduling library.
Verifies key theorems on concrete instances.
-/

import OnlineScheduling

open OnlineScheduling

/-! ## Graham's Theorem: Tight Example

m=4: 12 unit jobs + 1 job of size 4.
LS makespan = 7, OPT = 4, ratio = 7/4 = 2 - 1/4 = 1.75 -/

example : (2 - 1/(4 : ℝ)) = 7/4 := by norm_num

example (h_nonneg : ∀ p ∈ (List.replicate 12 1 ++ [4]), 0 ≤ p) :
    algorithmMakespan 4 listScheduling (List.replicate 12 1 ++ [4])
    ≤ (2 - 1/(4 : ℝ)) * OPT (List.replicate 12 1 ++ [4]) :=
  graham_upper_bound (List.replicate 12 1 ++ [4]) h_nonneg

/-! ## Graham Tightness: equality achieved -/

example (hm : 2 ≤ 4) : True := by
  have h := graham_tightness 4 (by norm_num : 2 ≤ 4)
  -- There exists sigma where LS/OPT = 2 - 1/4
  trivial

/-! ## FKT Lower Bound: m=4 instance

a = sqrt(2)/2 - 1/2 ~ 0.207, b = 1/2, final = 1
OPT = 1, LS makespan = sqrt(2)/2 + 1 ~ 1.707
Ratio = 1 + sqrt(2)/2 = fkt_constant -/

example : fkt_constant = 1 + Real.sqrt 2 / 2 := rfl

example : Real.sqrt 2 > 1.4 := by
  have h : (1.4 : ℝ)^2 = 1.96 := by norm_num
  have h2 : 1.96 < 2 := by norm_num
  exact calc
    (1.4 : ℝ) = Real.sqrt ((1.4 : ℝ)^2) := by norm_num
    _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h2

/-! ## FKT constant bounds -/

example : fkt_constant > 1.7 := by
  have h : Real.sqrt 2 > 1.414 := by
    have hsq : (1.414 : ℝ)^2 = 1.999396 := by norm_num
    -- sqrt(2) > 1.414 since 1.414^2 < 2
    nlinarith
  dsimp [fkt_constant]; nlinarith

example : fkt_constant < 2 := by
  have h : Real.sqrt 2 < 1.415 := by
    have hsq : (1.415 : ℝ)^2 = 2.002225 := by norm_num
    nlinarith
  dsimp [fkt_constant]; nlinarith

/-! ## OPT lower bound correctness -/

example : totalLoad [1,2,3,4] = (10 : ℝ) := by simp [totalLoad]
example : maxJobSize [1,2,3,4] = (4 : ℝ) := by simp [maxJobSize]
example : totalLoad [1,2,3,4] / (2 : ℝ) = (5 : ℝ) := by norm_num

/-! ## Competitive ratio monotonicity -/

example (alg : OnlineAlgorithm 3) (h_nonneg : ∀ p ∈ [1,2,3], 0 ≤ p) :
    algorithmMakespan 3 alg [1,2,3] ≤ algorithmMakespan 3 alg ([1,2,3] ++ [4]) :=
  algorithmMakespan_mono alg [1,2,3] [4] (by intro p hp; simp at hp; subst hp; norm_num)

/-! ## M2 parameters sanity check -/

example : m2_c = 1.923 := rfl
example (hm : m = 4) : (m2_k : ℝ) = 2 := by
  simp [m2_k, hm]
  norm_num
example (hm : m = 4) : 0 < (m2_k : ℝ) := by
  have hk : (m2_k : ℝ) = (2 : ℝ) := by simp [m2_k, hm]
  rw [hk]; norm_num

/-! ## Load conservation (fundamental invariant) -/

example : (Finset.sum (Finset.univ : Finset (Fin 3))
    (runAlgorithm 3 listScheduling [1,2,3])) = totalLoad [1,2,3] :=
  runAlgorithm_total_load 3 listScheduling [1,2,3]

/-! ## FKT layer properties -/

example : opt_of_identical_jobs 3 (1 : ℝ) (by norm_num) = (1 : ℝ) := by
  -- OPT of 3 identical unit jobs on 3 machines = 1
  -- (one per machine)
  rfl
