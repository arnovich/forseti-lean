# Rational slab-data proof checks

Task 248's optional producer `tools/aif_slab_data.py` checks symmetry of both
rational metric endpoints and both endpoint slopes with `decide +kernel`.
`AIFSlabData` lifts those four equalities through the existing Hermite metric
and metric-rate definitions. The two rational interval-width obligations also
use kernel decisions. Every polynomial check, matrix certificate and final
physical drift statement remains unchanged.

The existing slab generator and replay command remain unchanged. The new
producer requires explicit cells, writes under `.lake/`, and rejects an
unexpected original source shape. Its `--check` mode never repairs files.
Generated proposals still require Lean checking; generation is not evidence.

```sh
lake build
python3 tools/aif_slab_data.py /path/to/candidate.json.gz \
  --cell 3:200 --output-directory .lake/slab_data_example
python3 - <<'PYCODE'
import sys
from pathlib import Path
sys.path.insert(0, "tools")
from aif_replay import merge_setups, write_json

base = Path(".lake/build/ir/Gimle/Forseti/Tests")
setup = merge_setups([base / name for name in (
    "AIFSlab.setup.json", "AIFPolynomialBinding.setup.json",
    "AIFSlabData.setup.json",
)])
setup["name"] = "Gimle.Forseti.Examples.AIFPolynomialBin3Slab200"
write_json(Path(".lake/slab_data_example/cell.setup.json"), setup)
PYCODE
lake env lean -j1 -DElab.async=false \
  --setup .lake/slab_data_example/cell.setup.json \
  .lake/slab_data_example/AIFPolynomialBin3Slab200.lean
```

The explicit setup map resolves imports across the shared `Gimle` namespace.
A successful cell check reports three theorems using only `propext`,
`Classical.choice` and `Quot.sound`.

The candidate remains SHA-256
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.
Use the existing Lean 4.32.1 checking environment and its pinned dependencies.

In an isolated source comparison for bin 3, slab 200, the checked cell artifact
fell from 10,555,800 to 9,311,432 bytes. Including the 21,992-byte shared helper,
the proposal uses 9,333,424 bytes, approximately 11.6% less. This single-cell
storage result does not establish a speedup or a whole-mesh storage bound;
compiler timings were uncontrolled. The option is intended for further measured
storage work, and does not replace the existing producer by default.

Eight Lean regressions check accepted symmetric data, asymmetry in each of the
four matrix inputs, zero/negative time steps and reversed eta bounds. Portable
Python fixtures check complete source preservation at both bin/mesh extremes,
fail-closed shape checks and nonmutating verification. No new startup cell
coverage, trajectory theorem, production pin or checker enrollment is claimed.
