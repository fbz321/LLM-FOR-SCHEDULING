# Online Scheduling Lower Bounds (Lean 4)

Formal verification of lower bounds for the **online list scheduling problem**:

> P | online, list | Cmax — m identical parallel machines, jobs arrive one by one with no
> lookahead and must be irrevocably assigned on arrival. Goal: minimize makespan Cmax,
> performance measured by the competitive ratio ρ.

## Current gap

| Bound | Value | Source |
|-------|-------|--------|
| Lower | **1.880…** | Rudin (2003), asymptotic |
| Upper | **1.9201** | Bartal et al. / Fleischer–Wahl |
| **Gap** | **[1.880, 1.9201]** | |

## Structure

- [`OnlineScheduling/`](OnlineScheduling/) — Lean 4 formalization
  - `Algorithms/` — online algorithms (List Scheduling, M2, …)
  - `LowerBounds/` — adversary constructions and lower-bound proofs
    (Faigle–Kern–Turan, KnownSum, Rudin, …)
  - `Models/` — scheduling model variants (BinStretching, GoS, Decreasing, …)
- [`bottleneck_reflection/`](bottleneck_reflection/) — LLM-assisted proof bottleneck
  reflection loop (Python; uses DeepSeek/Claude API via `DEEPSEEK_API_KEY` /
  `ANTHROPIC_API_KEY` env vars)
- [`validation/`](validation/) — NL→Lean validation pipelines and results
- [`training/`](training/) — (historical) SFT/LoRA training configs for Lean proof generation

## Status

Formalized bounds:
- ✅ List Scheduling (Graham) upper bound
- ✅ Faigle–Kern–Turan lower bound (1 + √2/2 ≈ 1.707)
- ✅ Rudin asymptotic lower bound (1.88)
- ✅ P2/P3 adaptive adversary constructions
- ✅ KnownSum P2 4/3, P6 3/2 lower bounds
- ⬜ Rudin m=4 √3 lower bound (in progress)

## Build

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

```bash
lake build
```

CI runs the build on every push via `lean-action`.

## Contributing

This is a research repository; issues and PRs welcome. Proofs are checked by the
Lean kernel — please mark unfinished proofs explicitly (e.g. `sorry`).

## License

Apache-2.0 (proofs and formalization). See [LICENSE](LICENSE).
