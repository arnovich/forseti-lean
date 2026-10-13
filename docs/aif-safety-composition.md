# End-to-end AIF safety composition with explicit certificate obligations

`tools/aif_safety_composition.py` generates the final composition of the
original compiled AIF circuit, complete startup mesh propagation, the eight
checked terminal-entry certificates, and the local invariant region.

The main theorem remains conditional on two complete families of startup
certificates: in-tube drift and output enclosure for every one of the 8 x 370
candidate cells. These families have not yet been supplied. The theorem does
not assume a trajectory remains inside the tube: it derives membership from
zero initialization, the actual circuit derivatives, drift certificates and
exact mesh joins. Terminal membership then gives local entry at time 30.

Before time 30, the output certificates give x2 <= 16/5. After time 30, local
invariance gives the stronger x2 <= 5/2 for any later time. The composition
includes existence of an actual realization and nonnegativity of its compiled
output. Thus complete certificate families would imply universal safety on
the full forward domain, including the originally requested [0,100] horizon.
Existing forward uniqueness and specieswise nonnegativity remain available
from the same circuit-solution import.

This is a checked implication with outstanding certificate premises, not a
completed unconditional safety proof. It adds no drift/output cell coverage
and changes neither the production Asgard pin nor checker enrollment.

Generate with `python3 tools/aif_safety_composition.py --output-directory DIR`;
use `--check` for a nonmutating source comparison. The generated Lean module
must pass the separate replay and archived-context audit.
