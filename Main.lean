/-
OnlineScheduling Test Runner

Validates key theorems on concrete instances.
-/

import OnlineScheduling

open OnlineScheduling

def main : IO Unit := do
  let m : ℕ := 4
  -- Graham tight example: m*(m-1) unit jobs + 1 big job
  let σ : JobSequence :=
    List.replicate (m * (m-1)) 1 ++ [(m : ℝ)]

  IO.println "=== Online Scheduling Test ==="
  IO.println s!"m = {m}"
  IO.println s!"σ = {σ}"

  let loads := runAlgorithm m listScheduling σ
  let lmakespan := makespan m loads
  IO.println s!"LS makespan = {lmakespan}"

  let w := totalLoad σ
  let pmax := maxJobSize σ
  let lb := max pmax (w / (m : ℝ))
  IO.println s!"W = {w}, pmax = {pmax}"
  IO.println s!"OPT ≥ max(pmax, W/m) = {lb}"

  let ratio := lmakespan / lb
  let bound := 2 - 1 / (m : ℝ)
  IO.println s!"LS/LB = {ratio}"
  IO.println s!"Graham bound = {bound}"
  IO.println s!"≤ bound? {ratio ≤ bound}"

  IO.println ""
  IO.println "--- Known Bounds (Rudin 2003) ---"
  IO.println "m=2: LB=3/2, UB=3/2 (optimal)"
  IO.println "m=3: LB=5/3, UB=5/3 (optimal)"
  IO.println "m=4: LB≈1.7310, UB≈1.7333"
  IO.println "m→∞: LB≈1.8520, UB≈1.9201"
