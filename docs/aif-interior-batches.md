# AIF interior drift batches

Task 248's next selected-cell replay uses the [factored polynomial backend](aif-factored-tensor.md)
on two interior time slices. Each batch includes every parameter bin, with edges
`8, 8.5, 9, 9.5, 10, 10.5, 11, 11.5, 12`:

| Slab index | Physical time | Parameter bins |
| --- | --- | --- |
| 200 | `[13,13.1]` | 0–7 |
| 300 | `[23,23.1]` | 0–7 |

These sixteen cells are disjoint from the six early representative cells and
eight terminal cells checked previously. The immutable candidate and mathematical
checker are unchanged. Every cell retains 80 rational matrix certificates, two
polynomial bindings, both endpoint nonnegativity theorems and its physical drift
theorem. Equality checks use the ordinary Lean kernel.

## Reproduction

Use the pinned Lean toolchain and existing Lake setup maps, as described in
[resumable drift batches](aif-replay-batches.md). For each `SLAB` in `200 300`:

```sh
python3 tools/aif_replay.py /path/to/candidate.json.gz \
  --lean "$(lake env which lean)" \
  --setup .lake/build/ir/Gimle/Forseti/Tests/AIFSlab.setup.json \
  --setup .lake/build/ir/Gimle/Forseti/Tests/AIFPolynomialBinding.setup.json \
  --output-directory ".lake/aif_interior_batches/slab${SLAB}" \
  --cell "0:${SLAB}" --cell "1:${SLAB}" --cell "2:${SLAB}" --cell "3:${SLAB}" \
  --cell "4:${SLAB}" --cell "5:${SLAB}" --cell "6:${SLAB}" --cell "7:${SLAB}" --resume
```

Repeat with `--verify-only` in place of `--resume` to audit the saved receipts.
The two directories can run independently; each checks its cells sequentially
with one Lean thread. Keep the import environment fixed until both finish.
Concurrent batch timings are not a speedup measurement.

## Scope

The local drift theorem assumes `-3/200 ≤ e 2 ≤ 3/200`. These batches do not derive
that assumption from tube energy or bind the new slab definitions to the global
mesh. The earlier six cells have separate containment and mesh-transport proofs;
that result does not automatically extend to the new cells. All 2,960 cells have
geometric coverage and exact time joins, but those facts do not supply missing
local drift, containment, output bounds or trajectory invariance.

The full startup trajectory theorem remains open, including initial containment,
trajectory existence, the energy chain rule, typed circuit binding and terminal
continuation. The aim of these batches is to extend checked local drift evidence
into the interior of the startup interval without changing the mathematical model.

## Verified result

All sixteen complete modules pass: 1,280 matrix certificates, 32 polynomial
bindings, sixteen physical drift theorems and 48 exact named axiom reports.
Every report uses only `propext`, `Classical.choice` and `Quot.sound`.
The compiled cell artifacts total **169,705,040 bytes (169.71 MB)**.
Both eight-cell batches pass a fresh `--verify-only` run; all evidence file
modification times remain unchanged.

The exact-set audit checks the generated sources against the immutable candidate,
all receipt/source/setup/log/artifact hashes, artifact sizes, theorem names,
allowed axioms, successful exits and both verification logs. The two complete
checking environments agree and match the previously validated factored backend.
Their SHA-256 is
`525fd6640bd2745a18463daa373a6cf4f43a76980558979379ae7fff136b052e`.
The audit and evidence are retained under `.lake/aif_interior_batches/`, with
`verification.json`, `audit.py`, `run.py` and separate `slab200`/`slab300` directories.

The historical union is now **30 distinct local drift cells out of 2,960**;
2,930 cells still need local drift replay. This union combines these sixteen
fresh cells with fourteen earlier results. It does not claim that the earlier
receipts were refreshed for the changed shared backend. Containment and global
mesh transport remain established separately for only the original six cells.

No Lean or Python implementation changed in this milestone. The audit verifies
that implementation/configuration files match commit `5c2d600`, that the checking
environment is identical, and that the prior validation logs retain their hashes.
The earlier full build, demo, 49 Python tests and scoped tooling checks are retained
as validation evidence; they were not rerun for these documentation-only changes.
The three pre-existing Python formatting differences documented in the factored
backend milestone remain unchanged.

The mathematical-scope, integration and evidence panel found no remaining blockers.
Its audit findings were resolved by accepting both newly compiled and valid reused
receipts while comparing their contents exactly, rejecting compilation in
verification-only logs, and requiring successful historical records before counting
them. The prioritized synthesis is retained in `panel-review.json` alongside the
verified evidence.
