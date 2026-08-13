# Online Scheduling Lower Bounds (Lean 4)

Machine-checked formalization of lower bounds for the **online list scheduling problem**:

> **P | online, list | Cmax** — m identical parallel machines, jobs arrive one by one
> with no lookahead and must be irrevocably assigned on arrival. The goal is to
> minimize the makespan Cmax, and the performance of an online algorithm is measured
> by its competitive ratio ρ: for every input, Cmax(algorithm) ≤ ρ · OPT.

The central open problem: **close the gap between the best known lower bound and
upper bound for this classic problem**, ideally with fully verified proofs.

## Current gap

| Bound | Value | Source |
|-------|-------|--------|
| Lower | **1.880…** | Rudin (2003), asymptotic |
| Upper | **1.9201** | Bartal et al. / Fleischer–Wahl |
| **Gap** | **[1.880, 1.9201]** | open since 2003 |

For small m the bounds are nearly tight: m=2, 3 are settled at 3/2 and 5/3
respectively; for m=4 the best bounds are ≈1.7310 (lower) and 26/15 ≈ 1.7333
(Chen et al. 1994, upper).

## What has been done

The library contains **169 theorems/lemmas, 158 fully proved, 11 remaining
obligations** — every completed proof is checked by the Lean 4 kernel.

### Formalized lower bounds

| Model / adversary | Result | Status | File |
|---|---|---|---|
| Faigle–Kern–Turan (1989) | LB 1 + √2/2 ≈ 1.707 | ✅ | [LowerBounds/Faigle.lean](OnlineScheduling/LowerBounds/Faigle.lean) |
| Rudin (2003), m=4 | LB √3 (exact proof) | ✅ | [LowerBounds/Rudin.lean](OnlineScheduling/LowerBounds/Rudin.lean) |
| Rudin (2003), asymptotic | LB 1.88 (1 existence axiom remains) | ✅ | [LowerBounds/Rudin.lean](OnlineScheduling/LowerBounds/Rudin.lean) |
| Pseudo-lower-bound, m=4/5/6 | stage-based adversaries | ✅ | [LowerBounds/PseudoLowerBound.lean](OnlineScheduling/LowerBounds/PseudoLowerBound.lean) and M5/M6 variants |
| Pseudo-lower-bound, general m | Tan & Li (2015) 5-stage adversary (3135 lines) | ✅ | [LowerBounds/PseudoLowerBoundGeneral.lean](OnlineScheduling/LowerBounds/PseudoLowerBoundGeneral.lean) |
| Bin stretching | LB 4/3 | ✅ | [LowerBounds/BinStretchingLowerBound.lean](OnlineScheduling/LowerBounds/BinStretchingLowerBound.lean) |
| Known sum, P2 | LB 4/3 | ✅ | [LowerBounds/KnownSumLowerBound.lean](OnlineScheduling/LowerBounds/KnownSumLowerBound.lean) |
| Known sum, P6 | LB 3/2 | ✅ | [LowerBounds/KnownSumM6.lean](OnlineScheduling/LowerBounds/KnownSumM6.lean) |
| Grade of service | LB 5/3 (Park–Chang–Lee 2006 adversary) | ✅ | [LowerBounds/GoSLowerBound.lean](OnlineScheduling/LowerBounds/GoSLowerBound.lean) |
| Classic online P2/P3 | LB 3/2 | ✅ | [LowerBounds/ClassicOnline.lean](OnlineScheduling/LowerBounds/ClassicOnline.lean) |
| Decreasing jobs model | LB via decreasing adversary | ✅ | [LowerBounds/DecreasingLowerBound.lean](OnlineScheduling/LowerBounds/DecreasingLowerBound.lean) |

### Upper bounds (in progress)

| Algorithm | Result | Status |
|---|---|---|
| List Scheduling (Graham) | 2 − 1/m upper bound | ⚠️ 3 proof obligations |
| M2 algorithm (Albers) | improved UB for large m | ⚠️ 3 proof obligations |

### Current work: Braun–Graham (2025) m=4 additive bound

Formalizing Braun–Chung–Graham 2025 (J. Scheduling 28:529–544): for m=4, every
deterministic online algorithm has sequences with τ_A ≥ √3·τ_o − (2−√3) — an
**additive** lower bound that does not break the √3 multiplicative barrier.

- Definitions, layers, and all algebraic identities compile with 0 sorry
  ([BraunGraham2025.lean](BraunGraham2025.lean))
- Next: forced-schedule induction (Table 3), OPT packing (Table 7, residual
  invariant), then the main theorem

### Foundational work

- **v2 OPT foundation** — the original OPT axiom set was discovered to be
  *inconsistent* (it collapsed OPT to the average load; proved via an explicit
  contradiction in ProbeOPT.lean). [Basic.lean](OnlineScheduling/Basic.lean) was
  rebuilt on a sound basis (`scheduleLoads` + `optMakespan`, a concrete minimum
  over assignments) with 5 core theorems; 24 legacy files migrated.
- **Rudin construction repair** — numeric scanning exposed a mathematical bug in
  the raw Rudin step (the terminal layer lacks clamping: R_n can exceed 1, giving
  negative jobs). Fixed with a two-sequence construction (raw analysis +
  clamped AC/BC construction), including a tighter OPT bound
  OPT ≤ A_{n−1}+B_{n−1}+2·AC_n for the top layer.

## LLM-assisted proof development

This project doubles as a testbed for LLM-assisted formalization of scheduling
lower bounds.

### Phase 1: SFT fine-tuning (abandoned)

Fine-tuned 7B math models (deepseek-math-7b QLoRA, deepseek-prover-v2) on 172
NL→Lean samples across rounds R1–R10. Best pass@3: 3.3%. Conclusion: 7B models
cannot learn real proof capability from this sample size. Configs and results
kept in [training/](training/) and [validation/](validation/) for reproducibility.

### Phase 2: Bottleneck reflection (current)

Inspired by Ke et al. (ICML 2026), no training — instead a loop where the LLM
proposes adversary parameters → fills a Lean template → the Lean kernel verifies
→ errors feed back as "bottleneck reflections". Implementation in
[bottleneck_reflection/](bottleneck_reflection/).

Key experimental findings (E0–E3, DeepSeek chat / v4-pro):

- LLMs can produce the **correct adversary structure**, but Lean 4 **tactic-level
  details are unreliable** (E2 produced 403 lines with zero `sorry`, yet depended
  on lemmas with missing .olean files)
- The bottleneck-reflection loop converges on structural understanding but not
  on kernel-verified ρ-improvement below 1.88 so far

## Repository structure

```
OnlineScheduling/          Lean 4 library
  Algorithms/              online algorithms (LS, M2)
  LowerBounds/             adversary constructions and lower-bound proofs
  Models/                  model variants (BinStretching, GoS, KnownSum, Decreasing)
bottleneck_reflection/     LLM + Lean-kernel reflection loop (Python)
validation/                NL→Lean validation pipelines and results
training/                  (historical) QLoRA/SFT configs and logs
docs/                      THEOREMS_ARCHIVE.md (all 169 declarations),
                           ROADMAP.md (per-file gaps), experiment writeups
```

## Build

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake build
```

CI runs the build on every push via `lean-action`.

## Contributing

This is a research repository; issues and PRs are welcome. Proofs are checked by
the Lean kernel — remaining obligations are marked explicitly (`sorry` /
`*_proof_obligation` axioms) and listed in [docs/ROADMAP.md](docs/ROADMAP.md).

## License

Apache-2.0. See [LICENSE](LICENSE).
