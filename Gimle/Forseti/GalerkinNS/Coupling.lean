import Gimle.Forseti.GalerkinNS.Family
import Gimle.Asgard.Streams.Torus

/-! # The family's coupling is asgard-lean's cosine coupling

asgard-lean's `Streams.Torus.cosineCoupling` restates, over `ℚ`, the
ordered-pair coupling `Family.coefficient` of this module's Galerkin family,
and `Torus.transport_eq_cosine` says that the exponential-basis transport of
the vorticity stream agrees with it on even data up to the change to cosine
amplitudes. This file closes the loop the two repositories cannot close on
their own: the real coupling of the family is the cast of the rational
coupling of the stream, definitionally in each of its three factors. With it,
`NS.rhs_eq_family` is a statement about *this* family's field. -/
namespace Gimle.Forseti.GalerkinNS.Family

open Gimle.Asgard.Streams

/-- `Family.coefficient` is the cast of `Torus.cosineCoupling`. -/
theorem coefficient_eq_cosineCoupling (p q k : Wave) :
    coefficient p q k = ((Torus.cosineCoupling p q k : ℚ) : ℝ) := by
  rw [coefficient, Torus.cosineCoupling,
    show cross p q = Torus.cross p q from rfl, show lam p = Torus.lam p from rfl,
    show S p q k = Torus.S p q k from rfl]
  push_cast
  ring

#print axioms coefficient_eq_cosineCoupling
end Gimle.Forseti.GalerkinNS.Family
