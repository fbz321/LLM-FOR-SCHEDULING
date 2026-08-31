# m=5 structured search results

## Singleton positions in Rudin Table A2

The first neighborhood keeps all 71 exact integer jobs, all six five-job
mixed blocks, and the order of the blocks fixed.  It only chooses the position
of the singleton in each `4+1` block.  Hence the search contains exactly

```text
5^6 = 15,625
```

fixed sequences.

The exact game verifier checked the rational threshold

```text
1748334970307 / 1000000000000 = 1.748334970307
```

which is strictly larger than the value printed by Rudin,
`1.74833497030641`.  Prefix OPT values were addressed by the SHA-256 digest of
`(m, sorted exact integer prefix)`.  A cached value therefore cannot be reused
for a different prefix multiset.

Result:

```text
tested       15,625
passed       0
state range  72..208
```

The full machine-readable record is
[`singleton_permutations_above_rudin.json`](singleton_permutations_above_rudin.json).
This is a negative result only for this finite order-only neighborhood.  It
does not rule out size changes, layer surgery, or a construction with another
Type-3 layer.

## Regression checks

The same threshold-game implementation reproduces the established Rudin
baseline at `874167/500000 = 1.748334` using all 71 content-bound prefix OPT
entries:

```text
PASS
states             6,909
violating states   4,746
```

Run the local regressions with:

```text
python adversary_search/test_incremental_verify.py
python adversary_search/test_rudin_incremental.py
python adversary_search/test_m5_structured_search.py
```

## Late-interface shortlist

A second local-only stage perturbs four coupled late interfaces by exact
multipliers in `[0.999, 1.001]`: the last Type-2 singleton, all four equal
Type-3 base jobs, the Type-3 singleton, and the final job. It enumerates 6,560
non-identity configurations and ranks them using inexpensive necessary screens.
This stage is explicitly **not certifying** because altered suffixes require
new exact prefix OPT values.

Artifacts:

```text
late_interface_shortlist.json
late_interface_analysis.json
late_interface_opt_manifest.json
```

The exact-work manifest selects ten candidates. Prefixes 1--64 reuse
content-bound exact baseline values. A local pre-pass solved all 23 entries at
lengths 65--67 (18 by matching bounds, five by immediate decision search).
The remaining server batch contains **37 exact OPT computations**, all at
lengths 68--71:

```text
length 68:  9
length 69:  9
length 70:  9
length 71: 10
```

Use the resumable executor after copying this directory to the server:

```text
python run_opt_manifest.py --workers 32 --outer-jobs 4 --split-depth 9
```

It atomically updates `late_interface_opt_results.json`; restarting the same
command skips completed keys. `--shard INDEX/COUNT` can split the deterministic
manifest across independent machines, while the content hash is revalidated
before every solve.

All 60 distinct candidate-specific prefix OPT values were ultimately computed
locally, so no paid server run was needed. The first pre-pass solved 23 entries
at lengths 65--67, and the remaining batch solved all 37 entries at lengths
68--71. The exact checker then tested all ten selected candidates at

```text
1748334970307 / 1000000000000 = 1.748334970307
```

Result:

```text
complete candidates  10
passed                0
states per candidate  72
```

Every candidate has a scheduler escape path through all 71 jobs. The best
maximum ratio on these explicit escape paths is approximately
`1.7478110647740217`, attained at the final prefix, already below Rudin's
published value. The full records are in `late_interface_exact_check.json` and
all exact OPT results are in `late_interface_opt_results.json`.

## Complete late-interface multiplier grid

The full `6,560`-point grid has now been certified, closing the scope gap left
by the ten-candidate shortlist. A staged safe-denominator proof was used:

```text
total candidates                         6,560
basic-bound least-loaded escapes          6,061
initial survivors                           499
additional mixed exact/bound path escapes   218
remaining candidates                        281
mixed-bound threshold-game escapes           281
unresolved                                     0
passed                                         0
```

For the last 281 sequences, each unknown prefix OPT was replaced by the rigorous
lower bound

```text
max(largest job, ceil(prefix sum / 5)).
```

Known content-addressed exact OPT values were retained. Running the full
scheduler-placement recursion with these denominators gives the adversary an
*easier* game than the true one because every denominator is at most the true
OPT. Nevertheless, every candidate has a scheduler escape. The bounded games
visit 75--172 states each. Their largest ratio upper bound is

```text
125759586191744747937 / 71931059166370370000
= 1.7483349703064097...
< 1748334970307 / 1000000000000.
```

Thus all `6,560` explicit suffix rescalings fail rigorously without solving the
268 expensive final-prefix OPT instances. The unnecessary resumable exact run
was stopped. The final certificates are in
`late_interface_remaining_safe_game.json`; the earlier screen and accumulated
exact values remain in `late_interface_full_analysis.json`,
`late_interface_survivor_escape_check.json`, and
`late_interface_survivor_opt_results.json`.

This rules out exactly the stated four-group multiplier grid. It does not rule
out a finer grid, larger changes, coupled re-derivation of an entire layer, or a
new packing mechanism.

## Two-Type-3-shaped scaled-copy probe

The dissertation supplies the reverse Type-3 ratio map, but not enough state,
row-order, and packing information to reconstruct a certified two-Type-3 m=5
layering recurrence. Therefore this pilot makes only a finite-sequence claim:
it inserts an exact rationally scaled copy of the published five-job Type-3
block immediately before the original block. For `q=p/r>1`, all published jobs
are multiplied by `p` and the inserted block by `r`, so its relative scale is
exactly `1/q` with no per-job rounding.

The deterministic grid

```text
q = 1001/1000, 1002/1000, ..., 1100/1000
```

contains 100 explicit 76-job sequences. Each has a certified scheduler escape
path: along the least-loaded-machine path, the maximum of
`online makespan / basic OPT lower bound` is already strictly below
`1.748334970307`. Since exact OPT is at least this lower bound, the true ratio
on that path is no larger. Thus no candidate needs expensive prefix OPT work.

Artifact: `two_type3_scaled_probe.json`. This rules out only this scaled-copy
pilot and does **not** rule out a genuinely formula-derived second Type-3 layer.
Such a construction requires recovering or deriving the missing tableau state
transitions and five-machine packing constraints first.

## Terminal multiset orders

A separate exact order-only check enumerates all

```text
6! / 4! = 30
```

unique permutations of the published terminal multiset `AAAASF` (four equal
Type-3 base jobs, its singleton, and the final job), while preserving the first
65 jobs. Only nine new content-addressed prefix OPT values were needed, all
settled by matching lower and LPT upper bounds. Every order has an exact
least-loaded-machine escape below the target threshold:

```text
complete candidates  30
passed                0
```

Artifacts: `terminal_orders.json`, `terminal_orders_opt_results.json`, and
`terminal_orders_exact_check.json`. Together with the earlier per-block
singleton permutations, this closes another finite order-only neighborhood;
it says nothing about new job sizes or a new packing mechanism.

## Full late-interface interleavings

The larger order-only stage fixes jobs 1--60 and exhaustively interleaves the
last Type-2 block (`XXXXt`), published Type-3 block (`AAAAs`), and final job
(`f`) while preserving the entire job multiset. The number of distinct orders
is

```text
11! / (4! 4!) = 69,300.
```

Content addressing collapses their late prefixes to only 199 multisets; 19
were already cached and 180 additional exact OPT values were solved. The exact
threshold game at `1.748334970307` then gives:

```text
tested       69,300
passed       0
state range  72..76
```

Artifact: `late_interleavings_exact_check.json`. This is a substantially larger
finite order-only negative result: no reordering of those eleven published
late jobs crosses Rudin's displayed bound. New progress now requires changing
the job multiset or the packing mechanism.

## Type-2 4+1 size-split probe

A local structural-size probe changes exactly one of the five equal B jobs in
one of the five published Type-2 stages. The selected job uses an exact
multiplier `k/1000`, for every `k=900..1100` except identity; the other jobs are
multiplied by 1000 globally. Across five stages and five singleton positions,
this gives 5,000 candidates.

All 5,000 are rejected by a rigorous scheduler escape certificate: on the
least-loaded-machine path, `makespan / basic OPT lower bound` stays strictly
below `1.748334970307`. Thus no candidate-specific exact OPT computation is
needed. Artifact: `type2_split_probe.json`.

This closes the first one-job `5 → 4+1` size-surgery neighborhood. It does not
cover coupled changes to the remaining four B jobs, the following A/singleton
sizes, or a re-derived packing identity.

## Coupled final Type-2 block grid

A broader size-surgery grid jointly scales the final Type-2 block's five equal
B jobs, four equal A jobs, and singleton. Each of the three groups uses

```text
9950/10000, 9955/10000, ..., 10050/10000,
```

with the all-identity point omitted. This gives `21^3 - 1 = 9,260` explicit
sequences while preserving the published Type-3 block and final job.

```text
total candidates                    9,260
basic-bound least-loaded escapes     8,141
initial survivors                    1,119
mixed-bound threshold-game escapes   1,119
unresolved                               0
passed                                   0
```

For every survivor, the complete scheduler-placement recursion uses cached
exact OPT where available and the safe basic lower bound elsewhere. As in the
complete late-interface grid, this gives the adversary an easier game; a
scheduler escape remains a rigorous certificate for the true game. The games
visit 75--192 states. Their largest path-ratio upper bound is again the unchanged
prefix-60 value

```text
125759586191744747937 / 71931059166370370000
= 1.7483349703064097...
< 1.748334970307.
```

Artifact: `final_type2_coupled_safe_game.json`. Consequently the incomplete
candidate-specific final-prefix OPT computations are unnecessary and make no
contribution to this negative certificate.

This exhausts only this three-parameter, 0.05%-step grid around the published
final Type-2 block. It does not cover wider/finer changes, perturbations of
multiple Type-2 stages, or the coupled formula and packing changes required for
a genuinely new layer.

## Coupled grids across all Type-2 stages

The same B/A/singleton grid was applied separately to each of the five
published Type-2 stages. To keep every perturbation exact even when an early
stage's printed integer sizes are not divisible by 10,000, the complete
sequence is scaled by 10,000 and the selected stage uses its three multiplier
numerators directly. The grid contains

```text
5 × (21^3 - 1) = 46,300 candidates.
```

```text
total candidates                    46,300
basic-bound least-loaded escapes    40,693
initial survivors                    5,607
mixed-bound threshold-game escapes   5,607
unresolved                               0
passed                                   0
```

The 5,607 survivor games visit 6,945--12,299 states. Survivors by perturbed
stage are `1,131, 1,119, 1,119, 1,119, 1,119`. Their largest path-ratio upper
bound is

```text
1054856925963865625 / 603349440398708736
= 1.7483349703064101...
< 1.748334970307.
```

This maximum occurs at prefix 15 of the unchanged construction before the
first Type-2 perturbation can take effect. It is only about `5.90e-13` below the
strict search threshold, so decimal display precision must not be used for the
comparison; the certificate compares the exact fractions.

Artifacts: `type2_coupled_grid.json`, `type2_coupled_survivors.json`, and
`type2_coupled_safe_game.json`.

This closes all five one-stage, three-group local grids. It does not cover
simultaneous perturbations of multiple stages or a new recurrence/packing
identity.

## Coupled initial-block grid

The three equal five-job blocks at prefixes 1--15 were jointly perturbed with
the same 21-value multiplier grid. Exactness is maintained by scaling the full
sequence by 10,000 and applying integer numerators to the three selected
blocks. All `21^3 - 1 = 9,260` non-identity candidates are rejected directly by
the least-loaded scheduler path with the basic OPT lower bound; no second-stage
game or exact candidate OPT is needed.

The largest path-ratio upper bound is

```text
33218540441529816435631165 / 19000100670473869822263296
= 1.7483349703063091...
< 1.748334970307.
```

It occurs at prefix 71; every candidate's maximum occurs there. Artifact:
`initial_coupled_grid.json`.

This rules out only independent scaling of the three initial equal blocks on
the stated grid. It does not couple those changes to reconstructed Type-2
formulas or change multiplicities/order.

## Shared perturbation across all Type-2 stages

As a coordinated proxy for modifying the repeated layer mechanism, one common
B/A/singleton multiplier triple was applied simultaneously to all five Type-2
stages. The exact 21-value grid again has `9,260` non-identity candidates.

```text
total candidates                    9,260
basic-bound least-loaded escapes     8,141
initial survivors                    1,119
mixed-bound threshold-game escapes   1,119
unresolved                               0
passed                                   0
```

The bounded games visit 6,945--31,398 states. Their largest ratio upper bound
is the unchanged prefix-15 value

```text
1054856925963865625 / 603349440398708736
= 1.7483349703064101...
< 1.748334970307.
```

Artifacts: `all_type2_shared_grid.json`, `all_type2_shared_survivors.json`, and
`all_type2_shared_safe_game.json`.

This closes one coordinated three-parameter family, but it is not equivalent
to re-running Rudin's recurrence with altered parameters: every stage uses the
same relative multipliers and all other jobs remain published values. A new
bound now requires a more expressive change in recurrence, multiplicities, or
offline packing identities rather than another isolated local rescaling.

## Inserted Type-2-shaped block pilot

A ten-job copy of the final published Type-2 block (five B, four A, singleton)
was inserted immediately before the Type-3 block. For `q=p/r`, the published
sequence is scaled by `p` and the inserted block by `r`, so its relative scale
is exactly `1/q`. The grid `q=1.200,1.201,...,2.000` contains 801 explicit
81-job sequences.

```text
total candidates                      801
basic-bound least-loaded escapes       365
initial survivors                      436
basic-bound threshold-game escapes     436
unresolved                               0
passed                                   0
```

Every survivor's complete bounded game visits exactly 85 states. The largest
upper ratio on those escape paths is only

```text
124035018344733941032887 / 76475405198646660500000
= 1.621894228903398...
```

at prefix 76. Artifact: `inserted_type2_safe_game.json`.

This is deliberately a **Type-2-shaped** pilot, not a formula-derived sixth
Type-2 layer: downstream rows were not reconstructed and no tableau packing
claim is made. It rules out only this copied-block scale family. A meaningful
additional layer must be generated jointly with its successor sizes.
