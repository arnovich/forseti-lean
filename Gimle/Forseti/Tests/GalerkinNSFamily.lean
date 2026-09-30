import Gimle.Forseti.GalerkinNS.Family
import Gimle.Forseti.Examples.GalerkinNS.T3
import Gimle.Forseti.Examples.GalerkinNS.K5
import Gimle.Forseti.Examples.GalerkinNS.B2

/-! Coverage for the Galerkin Navier–Stokes family theorems.

The family theorems are applied to members `tools/galerkin_ns.py` does not emit
— a 2-mode list and a list holding a `±` pair — so they are seen to be
family-wide and not a restatement of the generated members. A concrete instance
of the energy identity is evaluated by hand on a 3-mode field with a real triad,
and the identity is shown to fail when the forced mode has `λ ≠ 2`: with the
forcing on `(1, 0)` its right-hand side is wrong at a concrete point. Each
generated member's `field_eq_family` and `decrease_family` are restated. The
axiom policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.GalerkinNSFamily

open Gimle.Forseti
open Gimle.Forseti.GalerkinNS
open Gimle.Asgard
open Gimle.Asgard.Dynamics

/-! ### Members the generator does not emit -/

/-- Two modes, the forced one first. -/
def two : Fin 2 → Family.Wave := ![(1, 1), (1, 0)]

theorem two_nonzero : ∀ i, two i ≠ 0 := by decide

/-- Three modes including the pair `(1, 0)`, `(-1, 0)`: outside the generator's
half-plane convention, but every theorem still applies. -/
def pair : Fin 3 → Family.Wave := ![(1, 0), (1, 1), (-1, 0)]

theorem pair_nonzero : ∀ i, pair i ≠ 0 := by decide

example (x : Point 2) :
    Family.rate two (Family.field 1 1 two 0) x = -2 * 1 * Family.enstrophy x + 1 * x 0 :=
  Family.energy_identity 1 1 two two_nonzero 0 rfl x

example (x : Point 3) :
    Family.rate pair (Family.field (1 / 3) 2 pair 1) x =
      -2 * (1 / 3) * Family.enstrophy x + 2 * x 1 :=
  Family.energy_identity (1 / 3) 2 pair pair_nonzero 1 rfl x

example (x : Point 3) :
    2 * (1 / 3) * (2 ^ 2 / (8 * (1 / 3) ^ 2) - Family.energy pair x) -
        Family.rate pair (Family.field (1 / 3) 2 pair 1) x =
      1 / 3 * (x 1 - 2 / (2 * (1 / 3))) ^ 2 +
        2 * (1 / 3) * ∑ i ∈ Finset.univ.erase 1, (1 - 1 / Family.lam (pair i)) * x i ^ 2 :=
  Family.certificate (1 / 3) 2 (by norm_num) pair pair_nonzero 1 rfl x

/-- Trapping for the 2-mode member at level `1 > f²/(8ν²) = 1/8`, from any
start with `E ≤ 1`, on any forward time domain. -/
example (time : TimeDomain) (x₀ : Point 2) (initial : Family.energy two x₀ ≤ 1) :
    (∃ state, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ state) ∧
    (∀ x y : Signal 2, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ x →
      Nonlinear.Solves (Family.field 1 1 two 0) time x₀ y → Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ state →
      ∀ t ∈ time.domain, Family.energy two (state t) ≤ 1) :=
  Family.trapped 1 1 (by norm_num) two two_nonzero 0 rfl 1 (by norm_num) time x₀ initial

/-- Existence alone for the `±` member, at level `5 > 2²/(8/9) = 9/2`. -/
example (time : TimeDomain) (x₀ : Point 3) (initial : Family.energy pair x₀ ≤ 5) :
    ∃ state, Nonlinear.Solves (Family.field (1 / 3) 2 pair 1) time x₀ state :=
  Family.exists_solution (1 / 3) 2 (by norm_num) pair pair_nonzero 1 rfl 5 (by norm_num)
    time x₀ initial

example : ContDiff ℝ 1 (Family.field (1 / 3) 2 pair 1) := Family.contDiff_field _ _ _ _

/-! ### A concrete instance, evaluated by hand -/

/-- T3's modes, a real triad: the couplings are nonzero and cancel in `E'`. -/
def triad : Fin 3 → Family.Wave := ![(1, 0), (1, 1), (2, 1)]

/-- The ordered-pair coupling by hand: `c((1,1), (2,1), (1,0)) = (1·1 − 1·2)/(2·2) ·
[(1,1) − (2,1) = −(1,0)] = −1/4` and `c((2,1), (1,1), (1,0)) = (2·1 − 1·1)/(2·5) ·
[(2,1) − (1,1) = (1,0)] = 1/10`; summed over both orders, `−3/20`, which is
`T3.lean`'s coefficient of `a11 a21` in `a10'`. -/
example : Family.coefficient (1, 1) (2, 1) (1, 0) = -1 / 4 := by
  simp [Family.coefficient, Family.S, Family.cross, Family.lam]
  norm_num

example : Family.coefficient (2, 1) (1, 1) (1, 0) = 1 / 10 := by
  simp [Family.coefficient, Family.S, Family.cross, Family.lam]
  norm_num

/-- `E'` at `(1, 2, 3)` with `ν = 1`, `f = 1`: `−2·14 + 2 = −26`, computed from the
field directly (27 coupling terms), not through the theorem. -/
example : Family.rate triad (Family.field 1 1 triad 1) ![1, 2, 3] = -26 := by
  simp [Family.rate, Family.field, Family.coefficient, Family.S, Family.cross, Family.lam,
    Fin.sum_univ_succ, triad]
  norm_num

/-- The same value through the theorem. -/
example : Family.rate triad (Family.field 1 1 triad 1) ![1, 2, 3] = -26 := by
  rw [Family.energy_identity 1 1 triad (by decide) 1 rfl]
  simp [Family.enstrophy, Fin.sum_univ_succ]
  norm_num

/-- `λ(k forced) = 2` is what the identity uses: forcing `(1, 0)` instead, the
forcing enters `E'` as `2 f a_forced / λ = 2 f a_forced`, so the right-hand side
`−2νZ + f a_forced` is off by `f a_forced` at `(1, 2, 3)`. -/
example : Family.rate triad (Family.field 1 1 triad 0) ![1, 2, 3] ≠
    -2 * 1 * Family.enstrophy ![1, 2, 3] + 1 * (![1, 2, 3] : Point 3) 0 := by
  simp [Family.rate, Family.field, Family.coefficient, Family.S, Family.cross, Family.lam,
    Family.enstrophy, Fin.sum_univ_succ, triad]
  norm_num

/-! ### The generated members are instances -/

example : Nonlinear.field Examples.GalerkinNS.T3.compiled =
    Family.field (1 / 10) (1 / 1) Examples.GalerkinNS.T3.modes Examples.GalerkinNS.T3.forcedIndex :=
  Examples.GalerkinNS.T3.field_eq_family

example : Examples.GalerkinNS.T3.modes = ![(1, 0), (1, 1), (2, 1)] := rfl
example : Examples.GalerkinNS.T3.forcedIndex = 1 := rfl
example : Examples.GalerkinNS.B2.forcedIndex = 5 := rfl
example : Examples.GalerkinNS.B2.modes Examples.GalerkinNS.B2.forcedIndex = (1, 1) :=
  Examples.GalerkinNS.B2.modes_forced

example (x : Point 3) :
    Examples.GalerkinNS.T3.trapping.rate (Nonlinear.field Examples.GalerkinNS.T3.compiled) x ≤
      Examples.GalerkinNS.T3.trapping.alpha *
        (Examples.GalerkinNS.T3.trapping.inner - Examples.GalerkinNS.T3.trapping.energy x) :=
  Examples.GalerkinNS.T3.decrease_family x

example (x : Point 12) :
    Examples.GalerkinNS.B2.trapping.rate (Nonlinear.field Examples.GalerkinNS.B2.compiled) x ≤
      Examples.GalerkinNS.B2.trapping.alpha *
        (Examples.GalerkinNS.B2.trapping.inner - Examples.GalerkinNS.B2.trapping.energy x) :=
  Examples.GalerkinNS.B2.decrease_family x

/-- By proof irrelevance; what this pins is that both routes prove the same
statement, since the `rfl` only type-checks when the two types coincide. -/
example : @Examples.GalerkinNS.K5.decrease = @Examples.GalerkinNS.K5.decrease_family := rfl

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.GalerkinNS.Family.energy_antisymm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.energy_antisymm

/--
info: 'Gimle.Forseti.GalerkinNS.Family.cubic_flux_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.cubic_flux_zero

/--
info: 'Gimle.Forseti.GalerkinNS.Family.energy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.energy_identity

/--
info: 'Gimle.Forseti.GalerkinNS.Family.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.certificate

/--
info: 'Gimle.Forseti.GalerkinNS.Family.decrease'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.decrease

/--
info: 'Gimle.Forseti.GalerkinNS.Family.contDiff_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.contDiff_field

/--
info: 'Gimle.Forseti.GalerkinNS.Family.exists_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.exists_solution

/--
info: 'Gimle.Forseti.GalerkinNS.Family.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.unique

/--
info: 'Gimle.Forseti.GalerkinNS.Family.invariant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.invariant

/--
info: 'Gimle.Forseti.GalerkinNS.Family.trapped'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.trapped

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.field_eq_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.field_eq_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.decrease_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.decrease_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.field_eq_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.field_eq_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.decrease_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.decrease_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.field_eq_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.field_eq_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.decrease_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.decrease_family

end Gimle.Forseti.Tests.GalerkinNSFamily
