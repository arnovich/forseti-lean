import Gimle.Asgard.Examples.BurgersSquare
import Gimle.Asgard.Examples.PolynomialHeat

/-! The asgard-lean Burgers example is part of this release's build, so a
notebook that imports it finds it compiled. Nothing here is a Forseti
statement: the formal Burgers stream is asgard-lean's (task 060, v1.8.0). -/

namespace Gimle.Forseti.Tests.Burgers

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Burgers Gimle.Asgard.Examples.BurgersSquare

example : stream .ogf ν (ofPoly .ogf (MvPolynomial.X 1 ^ 2)) (Finsupp.single 0 1) = 1 / 5 :=
  coeff_t

/--
info: 'Gimle.Asgard.Streams.Burgers.candidate_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.candidate_stream

end Gimle.Forseti.Tests.Burgers
