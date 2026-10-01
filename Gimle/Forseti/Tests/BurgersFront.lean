import Gimle.Asgard.Examples.BurgersFront

/-! The asgard-lean Cole–Hopf front is part of this release's build, so a
notebook that restates its certified truncation, the identification of its
analytic field with `1/(1 + e^(x − t/2))` on the box, the band `2/5 ≤ u ≤ 3/5`
and the refuted `u ≤ 27/50` finds them compiled. Nothing here is a Forseti
statement: the theorems are asgard-lean's (tasks 061 and 062, v1.10.0). -/

namespace Gimle.Forseti.Tests.BurgersFront

open Gimle.Asgard.Streams Gimle.Asgard.Examples.BurgersFront

example : tailBound (ColeHopf.frontMajorant ν terms r hr) box N = 1 / 16384 := error_eq

example {x : Fin 2 → ℝ} (hx : box.Mem x) :
    analyticField .ogf (ColeHopf.front ν terms) x = 1 / (1 + Real.exp (x 1 - x 0 / 2)) :=
  front_field_eq hx

example : 27 / 50 < analyticField .ogf (ColeHopf.front ν terms) ![1 / 6, -1 / 8] :=
  front_corner_gt

/--
info: 'Gimle.Asgard.Examples.BurgersFront.bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.bound
/--
info: 'Gimle.Asgard.Examples.BurgersFront.front_field_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.front_field_eq
/--
info: 'Gimle.Asgard.Examples.BurgersFront.band'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.band
/--
info: 'Gimle.Asgard.Examples.BurgersFront.not_below'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.not_below

end Gimle.Forseti.Tests.BurgersFront
