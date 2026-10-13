# Whole-family AIF certificate checks

Task 248's optional `tools/aif_family_checks.py` producer uses kernel decisions
for entire finite families. It keeps both universally quantified validity
statements over the 40 matrix certificates at each endpoint, and both polynomial
binding statements over all matrix entries. It replaces their finite-case proof
construction without changing any coefficients, certificate definitions, model
bindings, or final physical drift statement.

The producer builds on [rational slab-data checks](aif-slab-data.md). It requires
explicit cells, writes only under `.lake/`, rejects unexpected upstream proof
shapes, and checks that every byte outside the replaced proof blocks agrees.
Its `--check` mode neither creates nor repairs generated files. Generation alone
is not proof; every proposed cell still requires Lean kernel checking.

```sh
python3 tools/aif_family_checks.py /path/to/candidate.json.gz \
  --cell 3:200 --output-directory .lake/family_check_example
```

Use the same Lean 4.32.1 environment and three explicit setup maps shown in the
[slab-data checking instructions](aif-slab-data.md). Set the setup name to the
generated cell's module name. Each successful cell check must report the two
endpoint nonnegativity theorems and `drift_bound_physical`, using only the allowed
standard axioms. Pinned dependencies and the candidate SHA remain unchanged.

For the checked bin 3, slab 200 pilot, the cell artifact decreased from 9,311,432
to 8,146,248 bytes. Both versions use the same 22,016-byte shared helper, giving
helper-inclusive totals of 9,333,448 and 8,168,264 bytes. This is a single-cell
storage result; it does not establish a speedup or whole-mesh storage bound.
The existing default producer and running replay batches remain unchanged.

Portable regressions check full data and binding preservation at both bin and
mesh extremes, rejection of missing or changed proof shapes, and nonmutating
verification. The optional encoding adds no new startup coverage, trajectory
result, production pin, or checker enrollment.
