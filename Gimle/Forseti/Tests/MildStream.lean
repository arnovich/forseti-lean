import Gimle.Forseti.MildVorticity
import Gimle.Asgard.Examples.MildBand
import Gimle.Asgard.Streams.MildTable
import Gimle.Asgard.Tests.MildTable

/-! Build and replay roots for the viscous notebook's exact carrier examples.
These coefficient facts are kernel-checked in Asgard; numerical evidence
never supplies their authority. Classical guarantees use the circuit contract. -/
namespace Gimle.Forseti.Tests.MildStream
open Gimle.Asgard.Streams
open Gimle.Asgard.Examples

/-- The actual circuit output's initial x mode is its exact heat exponential. -/
theorem heat_x : MildBand.ω (1 / 10) 0 (1, 0) = ExpPoly.Table.toExp [((1, 0), 1 / 2)] :=
  Gimle.Asgard.Tests.MildTable.heat_x

/-- The first interaction contains two cancelling exponentials. -/
theorem first_y : MildBand.ω (1 / 10) 1 (0, 1) =
    ExpPoly.Table.toExp [((1, 0), 5 / 8), ((3, 0), -5 / 8)] :=
  Gimle.Asgard.Tests.MildTable.first_y

/-- The second interaction contains the resonant polynomial term exactly. -/
theorem second_2x2y : MildBand.ω (1 / 10) 2 (2, 2) = ExpPoly.Table.toExp
    [((8, 0), -35 / 13), ((14, 0), 5 / 26), ((8, 1), -5 / 13), ((6, 0), 5 / 2)] :=
  Gimle.Asgard.Tests.MildTable.second_2x2y

#print axioms heat_x
#print axioms first_y
#print axioms second_2x2y
end Gimle.Forseti.Tests.MildStream
