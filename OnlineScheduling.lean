/-
Copyright (c) 2026 OnlineScheduling contributors.
Released under Apache 2.0 license.

# OnlineScheduling: Lean 4 Library for Online Scheduling Theory

Formalizes deterministic online scheduling on `m` identical parallel
machines with the makespan minimization objective.

## Quick Start

```lean
import OnlineScheduling
open OnlineScheduling
#check graham_upper_bound
```

## Module Map

| Module | Content |
|--------|---------|
| `Basic` | Jobs, machines, makespan, OPT, competitive ratio |
| `CompetitiveRatio` | Known bounds, utility lemmas |
| `Algorithms.ListScheduling` | Graham's LS algorithm (`2-1/m`) |
| `LowerBounds.Basic` | Adversary framework |
| `LowerBounds.Layers` | Layering method (type-1, type-2) |
| `LowerBounds.Faigle` | FKT lower bound (~1.707) |
| `LowerBounds.Rudin` | Rudin lower bound (~1.88) |
| `LowerBounds.BraunGraham2025` | Braun–Chung–Graham 2025: m = 4 additive lower bound √3·OPT − (2−√3) |
| `Models.Testing` | Scheduling with Testing |
| `Models.Scenarios` | Scenarios model |
| `Models.BinStretching` | Known OPT (bin stretching) |
| `Models.KnownSum` | Known total processing time |
| `Models.Decreasing` | Decreasing job sizes (semi-online) |
| `Models.GradeOfService` | Grade of Service (GoS) |
-/

import OnlineScheduling.Basic
import OnlineScheduling.CompetitiveRatio
import OnlineScheduling.Algorithms.ListScheduling
import OnlineScheduling.LowerBounds.Basic
import OnlineScheduling.LowerBounds.Layers
import OnlineScheduling.LowerBounds.Faigle
import OnlineScheduling.LowerBounds.Rudin
import OnlineScheduling.LowerBounds.ClassicOnline
import OnlineScheduling.LowerBounds.BinStretchingLowerBound
import OnlineScheduling.LowerBounds.KnownSumLowerBound
import OnlineScheduling.LowerBounds.PseudoLowerBound
import OnlineScheduling.LowerBounds.PseudoLowerBoundM5
import OnlineScheduling.LowerBounds.PseudoLowerBoundM6
import OnlineScheduling.LowerBounds.PseudoLowerBoundGeneral
import OnlineScheduling.LowerBounds.KnownSumP3
import OnlineScheduling.LowerBounds.KnownSumP3Three
import OnlineScheduling.LowerBounds.KnownSumM6
import OnlineScheduling.LowerBounds.KnownSumSmallM
import OnlineScheduling.LowerBounds.GoSLowerBound
import OnlineScheduling.LowerBounds.BraunGraham2025
import OnlineScheduling.Models.Testing
import OnlineScheduling.Models.Scenarios
import OnlineScheduling.Models.BinStretching
import OnlineScheduling.Models.KnownSum
import OnlineScheduling.Models.Decreasing
import OnlineScheduling.Models.GradeOfService
