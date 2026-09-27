# Active suspension through nested traces

[`ActiveSuspension.lean`](../Gimle/Forseti/Examples/ActiveSuspension.lean) proves
a total safety contract for a five-state suspension. The mechanical plant and
actuator each have an integrated feedback trace; an outer trace connects their
ports through a controller. The root theorem concerns this typed circuit and
its observation circuit.

## Model and claim

The independent [model](../Gimle/Forseti/Examples/SuspensionModel.lean) has state
`s = (qb, qw, vb, vw, f)`: body and wheel positions, velocities, and applied
actuator force. With road displacement `r` and actuator response rate `a`,

```text
qb' = vb
qw' = vw
vb' = -qb + qw - vb + vw + f/2
vw' = 2qb - 6qw + 2vb - 2vw - f + 4r
f'  = a(-qb + qw - vb + vw - f)
```

Masses are 2 and 1, suspension stiffness and damping are 2, and tire stiffness
is 4; there is no tire damper. This is a normalized mathematical benchmark,
not a calibrated vehicle. Road displacement is continuous on ℝ, with
`|r(t)| ≤ 1/1000` for `t ≥ start`; no road derivative is assumed.
The initial region is the Euclidean ball `Σ sᵢ² ≤ 1/100`.

For either fixed rate `a = 2` or `a = 5/2`, `standard_contract` and
`replacement_contract` prove:

- a trajectory exists for every admitted input;
- all trajectories agree on the forward domain;
- every trajectory satisfies `|qb-qw| ≤ 1`, `|f| ≤ 1`, and
  `|-qb+qw-vb+vw+f/2| ≤ 1` at every forward time.

The last quantity is body acceleration. Initialization wires are read only at
the start. Behavior before the start is unrestricted. The two rates are fixed
alternatives, not a switching or time-varying actuator theorem.

## Finding and checking the invariant

The initial, input and output bounds are defined before the search in the model
module. The optional standard-library Python script
[`search_suspension.py`](../tools/search_suspension.py) solves a rational
Lyapunov equation at the midpoint rate, rounds to a finite sequence of dyadic
grids, and tries five scales and powers of two for the disturbance multiplier.
Every operation uses integers or `Fraction`; LDL decompositions reject
nonpositive pivots exactly.

The first accepted storage, after **19 storage candidates**, is `V(s) = sᵀPs`:

```text
P = [ 30  -2   22   8  -1
      -2  51  -32  -6  -4
      22 -32   47  13   2
       8  -6   13   6   1
      -1  -4    2   1   2 ]
alpha = 1/40, beta = 4096
```

The generated [data](../Gimle/Forseti/Examples/SuspensionCertificateData.lean)
gives rational weighted-square decompositions of `P`, `100I-P`, the three
matrices `P-lᵢlᵢᵀ` for the output rows, and the two augmented supply matrices.
Lean recomputes every target from the hand-written model and checks every
entry with ordinary kernel reduction. The search and its duplicate model
coefficients have no proof authority. This is a feasible certificate, with no
claim of optimality; exhaustion would not refute the root goal.

## Composing the proof

`system_ports` and `system_law` prove correspondence between the actual nested
traces and the component equations. The actuator interface is a relational
equivalence, with initialization and derivative obligations. It does not
require global continuity of a hidden command, which can be arbitrary before
the start.

The plant storage `Ep = (qb-qw)² + 2qw² + vb² + vw²/2` satisfies
`Ep' = -2(vb-vw)² + f(vb-vw) + 4r vw`. The actuator storage `f²` has derivative
`2a(f command-f²)`. `combined_storage` explicitly combines these identities
with the derivative of the searched coupling quadratic `V-Ep-f²`. Component
energy inequalities alone would lose the information needed for those cross
terms; the behavior contracts retain the state derivatives.

Both supply decompositions establish
`V' ≤ beta r² - alpha V ≤ alpha(1-V)`. The generic
[`Dissipative.sublevel`](../Gimle/Forseti/Dissipative.lean) rule proves `V ≤ 1`
using an integrating factor. Initial inclusion and the three output
containments are checked separately. Existence and uniqueness come from
forced-linear analysis independently of this invariant.

`output_contract` accepts any implementation satisfying the parameterized
`ActuatorLaw` at a supported rate. The two concrete implementations instantiate
that same theorem and use the same storage matrix; each rate has its own supply
decomposition. The actuator implementation is not unfolded in the outer proof.
This is a concrete compositional example, not a universal feedback rule or a
claim about arbitrary actuators with similar scalar energy bounds.

## Reproduce

```sh
python3 tools/search_suspension.py --check
python3 -m unittest discover -s tools -p 'test_*.py'
lake build
lake build equation_demo
```

Run the search without `--check` to regenerate the proposal. Check mode reruns
the search and compares bytes without writing. Python is optional: the checked
Lean data is committed, so `lake build` needs no search execution.

The [Lean regressions](../Gimle/Forseti/Tests/ActiveSuspension.lean) cover a
nonzero boundary initial state, sinusoidal road, excluded inputs, changing
initial wires, pre-start behavior, wrong axes and corrupted/misbound square
certificates. Axiom guards permit only `propext`, `Classical.choice`, and
`Quot.sound`. These optional example modules do not alter the standalone
checker's admitted imports or Python Forseti's pinned checking environment.
