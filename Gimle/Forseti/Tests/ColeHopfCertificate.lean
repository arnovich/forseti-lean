module

public import Gimle.Forseti.ColeHopfCertificate

/-! Regression controls for data-bound Burgers compression budgets. -/

@[expose] public section

namespace Gimle.Forseti.Tests.ColeHopfCertificate
open Gimle.Forseti.ColeHopfCertificate

/-- An empty heat spectrum is the zero Burgers solution. -/
noncomputable def zero : Data 0 where
  frequencies := Fin.elim0
  original := Fin.elim0
  retained := Fin.elim0
  viscosity := 1
  horizon := 1 / 2
  tolerance := 0

/-- The degenerate zero-error request still checks all budget premises. -/
theorem zero_valid : zero.Valid := by
  constructor <;>
    norm_num [zero, Gimle.Forseti.ColeHopfFinite.moment,
      Gimle.Forseti.ColeHopfFinite.initialRadius, Gimle.Forseti.ColeHopfFinite.growth]

/-- The denominator guard cannot be omitted even for an identity reduction. -/
noncomputable def pole : Data 1 where
  frequencies := ![1]
  original := ![1]
  retained := ![1]
  viscosity := 1
  horizon := 1 / 2
  tolerance := 1

theorem pole_invalid : ¬ pole.Valid := by
  intro h
  have ha := h.original_safe
  norm_num [pole, Gimle.Forseti.ColeHopfFinite.moment, Fin.sum_univ_succ] at ha

#print axioms zero_valid
#print axioms pole_invalid
end Gimle.Forseti.Tests.ColeHopfCertificate
