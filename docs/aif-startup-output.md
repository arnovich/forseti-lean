# Physical AIF output bounds on startup prefixes

This research checkpoint connects the original compiled biochemical circuit to
the physical x2 bound of 16/5 on two closed startup intervals. For a fixed real
parameter and a supplied realization of that circuit, the checked conclusions are:

- Every eta in [8,12]: x2 is at most 16/5 at every time in [0,1/200].
- Every eta in [8,17/2]: x2 is at most 16/5 at every time in [0,21/200].

The observation is Asgard's compiled `AIF.output`, applied to the physical state.
The proof passes through exact shifted coordinates and the same moving tube used
by the drift certificates. Both time endpoints and the parameter-bin boundaries
are included.

The trajectory is still assumed through the circuit's `Realizes` relation. This
checkpoint does not construct a solution, prove uniqueness or nonnegativity, or
establish startup coverage through time 30 or the requested safety through time
100. Its time intervals are deliberately limited to the cells already composed
in [startup-prefix invariance](aif-startup-prefix.md).

## Concrete certificates

There are 28 output companions: all eight first-slab cells and the next twenty
cells in bin 0. Each imports its already-checked slab and exact mesh binding.
It computes an upper center bound from all four Hermite controls at each of the
two parameter edges, checks those bounds and the positive remaining gap, and
checks four rational weighted-square certificates for the scaled output margin.
That gives 112 matrix certificates and 56 named cell-level axiom reports.

`tools/aif_output_certificates.py` emits selected companions. It supports the same
cell selections and expanded/polynomial import modes as the existing generators.
For example:

```sh
python3 tools/aif_output_certificates.py --output-directory .lake/output-cells \
  --polynomial-binding --cell 1:0
```

`tools/aif_startup_output.py` emits the fixed composition of those 28 companions
with the checked circuit transport and startup invariance:

```sh
python3 tools/aif_startup_output.py --output-directory .lake/aif_startup_output
```

Both commands accept `--check` to compare existing bytes without writing files.
Generated source has no proof authority until checked by Lean. Reproduction of
this research context requires the archived prerequisites and import artifacts;
the Task #248 `startup-output` evidence archive records their hashes and the
successful checking context. The production Asgard pin and checker enrollment
remain unchanged.
