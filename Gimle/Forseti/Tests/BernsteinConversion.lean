import Gimle.Forseti.BernsteinConversion

/-! Small exact conversions: monomials, constants, duplicate terms, both axes and
the degree check. -/
namespace Gimle.Forseti.Tests.BernsteinConversion
open Gimle.Forseti.RationalPolynomial Gimle.Forseti.BernsteinConversion

-- `s` in degree two has Bernstein coefficients `0, 1/2, 1`.
example : (List.range 3).map (coefficient 2 0 time · 0) = [0, 1/2, 1] := by decide +kernel

-- A constant has the same coefficient at every index.
example : (List.range 4).map (coefficient 3 0 (constant (-7/11)) · 0) =
    [-7/11, -7/11, -7/11, -7/11] := by decide +kernel

-- `s u` on both axes: only the far corner of a (1, 1) table is one.
example : [coefficient 1 1 (mul time parameter) 0 0, coefficient 1 1 (mul time parameter) 0 1,
    coefficient 1 1 (mul time parameter) 1 0, coefficient 1 1 (mul time parameter) 1 1] =
      [0, 0, 0, 1] := by decide +kernel

-- Repeated monomials are summed, as evaluation does.
example : coefficient 1 0 [⟨1, 0, 2⟩, ⟨1, 0, 3⟩] 1 0 = 5 := by decide +kernel

-- The degree check rejects a term above either bound.
example : withinDegree 2 1 (mul (power time 2) parameter) = true ∧
    withinDegree 1 1 (mul (power time 2) parameter) = false ∧
    withinDegree 2 0 (mul (power time 2) parameter) = false := by decide +kernel

-- The falling-factorial binomial agrees with `Nat.choose`, including below `k`.
example : (List.range 10).map (binomial 9) = (List.range 10).map (Nat.choose 9) ∧
    binomial 2 5 = 0 := by decide +kernel

/-- info: 'Gimle.Forseti.BernsteinConversion.eval_eq_bernstein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_eq_bernstein

/-- info: 'Gimle.Forseti.BernsteinConversion.table_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms table_binding

/-- info: 'Gimle.Forseti.BernsteinConversion.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binding

end Gimle.Forseti.Tests.BernsteinConversion
