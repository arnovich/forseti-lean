# AIF output enclosure

`AIFOutputEnclosure` proves an exact route from moving-tube membership to the
shifted x2 bound of 6/5. The physical-coordinate theorem then identifies that
threshold with physical x2 at most 16/5.

The caller supplies an upper bound on all four Bernstein controls of each
parameter-edge Hermite center, plus four checked weighted-square certificates
for a scaled metric margin. If the center bound is `c`, the gap is `g = 6/5-c`.
The certificate target is `g² P - (1/40000) E₁₁`, where coordinate 1 is shifted
x2. A nonnegative gap and tube energy at most 1/40000 imply an output-coordinate
error in the closed interval [-g,g]. Adding the center bound gives the threshold.

The proof checks the exact cubic reconstruction of both the matrix margin and
the center controls. It includes physical endpoint slopes in the two interior
controls. Bounds on the endpoint centers alone would be insufficient.

This module is a generic certificate interface. It does not supply certificates
for any particular candidate cell, establish trajectory existence or invariance,
or prove the complete time-100 safety result. Concrete certificate generation
and composition with [startup invariance](aif-startup-prefix.md) are separate steps.

The regression proofs cover a sharp metric margin, both closed error boundaries,
an error beyond the boundary, rejection of a zero metric, and a cubic that
overshoots its endpoint values.
