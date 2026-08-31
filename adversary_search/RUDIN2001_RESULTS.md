# Rudin 2001 fixed-sequence validation

This directory records exact checks of three fixed job sequences transcribed from Tables A2--A4 of Eric Rudin's 2001 dissertation. The checks use integer job sizes, exact prefix OPT values, and the minimax scheduler recursion in `m4_search.py`.

## Status

| Machines | Jobs | Literature value | Strict threshold checked here | Status |
|---:|---:|---:|---:|---|
| 5 | 71 | 1.74833497030641 | 1.748334 | **PASS** |
| 6 | 91 | 1.77409792411 | 1.7740979 (intended) | **PARTIAL: 81/91 prefix OPTs** |
| 7 | 57 | 1.792667559 | 1.7926675 | **PASS** |

`m=6` has no final lower-bound conclusion in this repository. Only prefix OPT values 1 through 81 have been computed; prefixes 82 through 91 and the final minimax check remain outstanding.

## Artifacts

- `seeds/rudin2001_m{5,6,7}.json`: fixed sequences, scaled to exact integers.
- `results/rudin2001/cache/`: resumable exact prefix OPT caches. The `m=6` filename contains `.partial` deliberately.
- `results/rudin2001/logs/`: original execution transcripts. The complete logs end in `RESULT: PASS`; the partial `m=6` log ends after prefix 81.
- `check_rudin.py`: cache-aware validator and resumable driver.

The JSON `known_value` fields are literature metadata, not evidence. The verified claims above are only the rational thresholds printed by a completed `RESULT: PASS` run.

## Reproduce the completed checks

Run from the repository root with the project Python environment:

```bash
python adversary_search/check_rudin.py \
  --seed seeds/rudin2001_m5.json --tau 1.748334 \
  --cache adversary_search/results/rudin2001/cache/m5_prefix_opts.json \
  --cache-only

python adversary_search/check_rudin.py \
  --seed seeds/rudin2001_m7.json --tau 1.7926675 \
  --cache adversary_search/results/rudin2001/cache/m7_prefix_opts.json \
  --cache-only
```

Both cached checks complete in under a second after loading the prefix OPTs. To inspect the incomplete run without starting expensive computation:

```bash
python adversary_search/check_rudin.py \
  --seed seeds/rudin2001_m6.json --tau 1.7740979 \
  --cache adversary_search/results/rudin2001/cache/m6_prefix_opts.partial.json \
  --cache-only
```

This exits with status 2 and prints the missing prefixes. Omit `--cache-only` to resume, recognizing that late prefixes have already taken hours each.

## Limitations

These are computational validations of fixed finite sequences, not Lean formalizations. The source tables should be independently checked against the dissertation before treating the decimal transcription as archival. In particular, the `m=6` seed notes that Table A3 was read from a rendered page.
