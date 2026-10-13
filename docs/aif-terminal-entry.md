# Eight exact candidate terminal-entry certificates

`tools/aif_terminal_entry.py` generates certificates for slab 369 of each of
the eight parameter bins in the existing candidate mesh. It imports the mesh
rather than copying or interpolating candidate data again. The shared rational
energy evaluator is proved equal to the real local Lyapunov quadratic.

For each bin, Lean checks an exact weighted-square certificate for the terminal
metric minus I/50, the two endpoint-center energy bounds V <= 1/400, nonzero
step and increasing eta edges, and the exact terminal time 30. The generic
local-entry bridge then proves V <= 3/400 < 1/100 from membership in that exact
candidate tube at time 30, for every eta in the bin's closed interval.

Successful replay produces 58 standard-axiom reports: two rational/real binding
lemmas and seven checks/theorems per bin. The eight matrix certificates and
sixteen center bounds are entry evidence, not additional drift cells. Generation
alone is not proof authority; the generated sources must pass Lean and the
archived-context audit.

This checkpoint does not prove that the physical zero-start trajectory reaches
the terminal tubes. Complete startup membership and typed-circuit continuation
remain separate composition obligations. The production Asgard pin and checker
enrollment are unchanged.

Generate with `python3 tools/aif_terminal_entry.py --output-directory DIR`.
Add `--check` to compare existing files without modifying them. The committed
Python tests cover complete bin generation and nonmutating check behavior;
proof replay additionally validates every generated theorem and its dependencies.
