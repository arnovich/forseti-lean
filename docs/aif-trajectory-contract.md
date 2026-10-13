# Typed AIF trajectory contracts

`tools/aif_trajectory_contract.py` generates contracts for the original compiled
AIF feedback followed by its compiled second-species observer. The root uses
Forseti's existing `Trajectory.Contract`: it supplies existence, uniqueness on
the forward time domain, and safety for every related output.

The admitted input fixes the real eta driver and sets all four physical species
to zero initially. As Asgard's feedback semantics requires, the initial wires
are constrained only at time zero; their later values are irrelevant. The proof
uses `Initialized` and `close_rel_reads_start`, and exhibits the declared input
as a witness to avoid an empty precondition.

After successful Lean replay, `startup_contract` gives output in `[0,16/5]`
on `[0,21/200]` for every fixed eta in `[8,12]`, with no assumed trajectory,
tube membership or missing cell certificate. The separate `forward_contract`
and `hundred_contract` preserve both complete drift and output certificate
families as explicit premises. They do not establish unconditional full-horizon
safety until the remaining concrete cells have been checked.

The generated regressions reject a changed initial species value and a varying
eta driver, accept initial wires that change after time zero, instantiate both
parameter endpoints, and derive an actual safe behavior for the declared input.
Existence and uniqueness come from the previously checked circuit-solution
results, independently of the quantitative safety certificates.

The replay imports the archived uniform-prefix theorem and preserves its
compiler and import fingerprints. Each compiler invocation has a completion
receipt, exact source/artifact hashes and an audited axiom report. Python
`--check` tests verify that source checking neither creates missing artifacts
nor repairs changed ones. No checker enrollment or production pin change is
part of this research contract.
