import Gimle.Asgard.Examples.BurgersFront

/-! The asgard-lean Cole–Hopf front is part of this release's build, so a
notebook that restates its certified truncation finds it compiled. Nothing
here is a Forseti statement: the certificate is asgard-lean's (task 061,
v1.9.0). -/

namespace Gimle.Forseti.Tests.BurgersFront

open Gimle.Asgard.Streams Gimle.Asgard.Examples.BurgersFront

example : tailBound (ColeHopf.frontMajorant ν terms r hr) box N = 1 / 16384 := error_eq

/--
info: 'Gimle.Asgard.Examples.BurgersFront.bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.bound

end Gimle.Forseti.Tests.BurgersFront
