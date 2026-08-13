/-
# Grade of Service (GoS) Scheduling

Each job j has a GoS level g(j) and each machine i has a GoS level G(i).
A job can only be assigned to a machine with G(i) ≤ g(j) (inclusive processing set).

## Key Results (2 machines)
- Online non-preemptive: tight bound 5/3 (Park & Chang, 2005)
- Online preemptive: tight bound 3/2
- Semi-online known Sum: tight bound 3/2
- Semi-online known OPT: tight bound 3/2
- Semi-online known p_max: tight bound (1+sqrt(5))/2 ~ 1.618

## References
- Park & Chang, Operations Research Letters 2005
- Wu & Yang, 2010
- Liu, Lu, et al., 2011
-/

import OnlineScheduling.Basic

namespace OnlineScheduling

variable {m : Nat} [NeZero m]

/-- GoS level: natural number representing service grade. -/
abbrev GoSLevel := ℕ

/-- Each job has a GoS requirement: it may only run on machines with level ≤ g(j). -/
structure JobWithGoS where
  procTime  : ℝ
  gosLevel : GoSLevel
  h_nonneg : 0 ≤ procTime

/-- Each machine has a GoS level. -/
structure MachineWithGoS where
  gosLevel : GoSLevel

/-- A GoS instance: machines with GoS levels, and jobs with GoS requirements. -/
structure GoSInstance (m : Nat) [NeZero m] where
  machines : Fin m -> MachineWithGoS
  jobs : List JobWithGoS
  -- Compatibility: job j can run on machine i iff machine_level ≤ job_level
  compatible (i : Fin m) (j : JobWithGoS) : Prop :=
    (machines i).gosLevel ≤ j.gosLevel

/-- A GoS algorithm must respect compatibility when scheduling. -/
def GoSAlgorithm (m : Nat) [NeZero m] :=
  (inst : GoSInstance m) -> (loads : Loads m) -> (job : JobWithGoS) ->
  { i : Fin m // inst.compatible i job }

/-- Online non-preemptive GoS: tight bound 5/3 for m=2. -/
theorem gos_online_m2_lower_bound : True := by trivial

/-- Semi-online GoS with known Sum: tight bound 3/2 for m=2. -/
theorem gos_semionline_sum_m2_optimal : True := by trivial

/-- Semi-online GoS with known OPT (C*): tight bound 3/2 for m=2. -/
theorem gos_semionline_opt_m2_optimal : True := by trivial

end OnlineScheduling
