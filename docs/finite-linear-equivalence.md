# Finite linear output equivalence

For two autonomous rational linear systems, set
`yᵢ(n) = dotProduct cᵢ ((Aᵢ ^ n).mulVec xᵢ)` and `m = d₁ + d₂`.
The initial vectors and linear readouts are fixed. Equality of outputs at
indices `0 ≤ n < m` is equivalent to equality at every natural index.
Both dimensions may be zero; a zero-dimensional system has identically zero output.

The [property module](../Gimle/Forseti/FiniteLinearEquivalence.lean) supplies
`Gimle.Forseti.FiniteLinearEquivalence.matrix_prefix_iff_all` and
`matrix_distinguishing_index`. The latter turns any output disagreement into
a disagreement before index `m`. Its definition `matrix_output` uses exact
rational arithmetic and observes initialization at time zero.

The proof reduces the comparison to one linear observation on a product state
space. Cayley–Hamilton expresses every transition power as a linear combination
of the first `m` powers. This is a known finite-dimensional linear algebra result;
the module makes its assumptions and matrix interpretation explicit in Lean.

The [regressions](../Gimle/Forseti/Tests/FiniteLinearEquivalence.lean) exercise
different-dimensional Fibonacci realizations, empty state spaces, a hidden
growing coordinate, changed initialization, and a nilpotent transition whose
first differing observation occurs at the end of the required prefix.

```sh
lake build Gimle.Forseti.FiniteLinearEquivalence Gimle.Forseti.Tests.FiniteLinearEquivalence
```

This is output equivalence for the specified initialization and readout, not
state-space conjugacy or equality for every initialization. It does not transfer
hidden-state boundedness. The bound requires linear transitions and readouts;
an affine representation needs its additional homogeneous coordinate counted.
Approximate numerical equality is not the premise of the theorem.

The module is a property theorem about rational matrices. The optional
[compiled circuit and Hoare bridge](linear-circuit-equivalence.md) connects
recognized original expressions to initialized execution and existing predicate
invariants. Enrollment through an external Forseti checking environment remains
a separate obligation. Neither module expands the checker's admitted interface.
