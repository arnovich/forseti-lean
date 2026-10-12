# AIF startup-prefix invariance

The research generator `tools/aif_startup_prefix.py` composes checked startup
cells for a realization of the original compiled Asgard AIF circuit. A fixed
parameter and the same trajectory are used throughout each composition.

The checked conclusions are:

- For every real eta in [8,12], one of the eight parameter bins contains its
  shifted trajectory in the moving tube for every time in [0,1/200].
- For every real eta in [8,17/2], the shifted trajectory stays in the moving tube
  over 21 consecutive cells, covering [0,21/200].

Both intervals include their final endpoint. Every included cell supplies a
checked drift theorem. Zero physical initialization gives exact zero initial
tube energy, and shared mesh nodes transfer the energy bound across each join.
The tube threshold is 1/40000.

These are conditional trajectory results: they assume the compiled feedback's
`Realizes` relation. They do not establish that a realization exists, is unique
or nonnegative, or satisfies the requested x2 bound through time 100. The full
startup mesh extends to time 30 and contains 2,960 cells.

## Checked components

This checkpoint adds 26 local drift certificates, 26 error-containment
companions, and 26 bindings to the exact candidate mesh. The new cells are the
first cell in bins 1 through 6 and cells 1 through 20 in bin 0; the first cells
in bins 0 and 7 were already checked. The historical totals at this checkpoint
are 56 local drift certificates, 48 containment companions, and 48 mesh bindings.
These counts describe different proof stages and must not be added together.

The emitted Lean module checks the prefix geometry, requires a drift theorem for
every cell, and uses the generic mesh composition theorem with the actual circuit
derivative transport. The explicit parameter-coverage theorem selects a fixed
bin before quantifying over time. The 21-cell theorem returns a containing cell
for each time, including the last mesh endpoint.

## Reproduction and scope

```sh
python3 tools/aif_startup_prefix.py --output-directory .lake/aif_startup_prefix/invariance
```

Use `--check` to compare existing generated source without writing files.
Generation is not proof checking. The Task #248 `startup-prefix` evidence archive
contains the checked sources, import maps, compiler logs, artifacts, and audits.
It records the exact candidate SHA-256 and links the prerequisite circuit
transport, initial membership, mesh, and containment evidence. Replaying needs
those prerequisite artifacts in the recorded checking context.

As with [circuit transport](aif-circuit-transport.md), this is an archived research
binding. The production Asgard dependency pin and default checker are unchanged.
The remaining work includes broader cell coverage, output enclosure, trajectory
existence/uniqueness/nonnegativity, and terminal continuation.
