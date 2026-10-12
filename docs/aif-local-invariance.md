# AIF local tube invariance

[`AIFInvariance.lean`](../Gimle/Forseti/Examples/AIFInvariance.lean) proves that a
supplied fixed-parameter AIF solution stays inside a slab's moving metric tube if
it starts inside and that slab has the checked in-tube drift bound.

`sublevel_of_boundary_derivative` is the scalar rule. It takes derivatives within
`[a,b]`, an initial value at most the bound, and a strictly negative derivative
whenever the value equals the bound on `[a,b)`. The derivative contract supplies
continuity on the closed interval. Mathlib's
`image_le_of_deriv_right_lt_deriv_boundary` then gives the bound through `b`.
Converting the derivative to a right derivative uses only a neighborhood within
`[a,b]`; no solution extension beyond either endpoint is assumed.

`tube_invariant` applies this rule to the existing `tubeEnergy`, using the
[physical-time chain rule](aif-energy-chain-rule.md). At energy `1/40000`, the
checked drift inequality gives a rate at most `-1/16000000`, hence strictly
negative. The proof invokes the certificate at the boundary; it never assumes
that the whole trajectory lies in the tube.

The slab theorem explicitly requires:

- Positive physical slab width and ordered eta endpoints.
- One fixed parameter in that slab's closed parameter interval.
- Component ODE derivatives for the supplied state on the closed time interval.
- The same in-tube drift interface exported by the checked mesh bindings.
- Initial energy at most `1/40000` at the slab's left endpoint.

The conclusion is energy at most `1/40000` throughout that closed slab. Existence,
uniqueness, initial membership from zero startup, typed-circuit binding, full
certificate coverage and composition across time slabs remain separate. This
is a local trajectory theorem with explicit solution and initial-set premises;
it does not establish the requested startup bound on `[0,100]`.

[`Tests/AIFInvariance.lean`](../Gimle/Forseti/Tests/AIFInvariance.lean) checks starts
on the boundary, a degenerate scalar interval, and the AIF interface at all three
saved widths. It also proves a counterexample to replacing strict boundary drift
by nonpositive drift: `t^3` starts at zero with derivative zero at the boundary,
but exceeds zero on `[0,1]`.

The rule is instantiated for all sixteen previously verified interior cells:
parameter bins 0–7 at slab indices 200 and 300, physical intervals `[13,13.1]`
and `[23,23.1]`. Each theorem imports its exact mesh binding and discharges the
geometric and drift premises using the existing checked results. Supplied ODE
derivatives and initial tube membership remain premises. These separate local
results do not show that a zero-initialized startup solution reaches those tubes.

The generated `AIFInteriorLocalInvariance` module has sixteen successful named
axiom reports and a 75,008-byte artifact, additional to its checked imports.
Evidence under `.lake/aif_local_invariance/` includes `concrete.py`, generated
source, setup map, checking-environment fingerprint, logs and receipt. The audit
links the archived mesh verification and binding-stage environment, all 26 prior
module receipts, freshly regenerated bindings, the new invariance implementation,
and the final application artifacts. It rehashes the complete checking environment.
The existing totals of 30 drift cells, 22 conditional coordinate-containment
results and 22 mesh transports are unchanged.

Validation passes under Lean 4.32.1: the two generic lemmas, three named regression
proofs, sixteen concrete applications, `lake build` (742 axiom reports),
`lake build equation_demo` (63 reports), all 57 Python tests, and build-path and
suspension checks. All reports use only `propext`, `Classical.choice` and
`Quot.sound`; no Lean warnings or errors remain. The required mathematical,
integration and evidence panel found no blockers after validation and provenance
checks. Its synthesis and the consolidated record are `panel-review.json` and
`verification.json` in the evidence directory.

The [mesh-composition theorem](aif-mesh-composition.md) now propagates local bounds
through exact joins, and the saved shifted startup state has checked zero initial
energy in all eight bins. Complete drift coverage and the remaining circuit and
trajectory obligations are still required.
