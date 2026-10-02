import Gimle.Forseti.GalerkinNS.Family
import Gimle.Forseti.Examples.GalerkinNS.T3
import Gimle.Forseti.Examples.GalerkinNS.K5
import Gimle.Forseti.Examples.GalerkinNS.B2
import Gimle.Forseti.Examples.GalerkinNS.T3S

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

/-! ### The enstrophy ball, on the same members -/

example (x : Point 2) :
    Family.zrate (Family.field 1 1 two 0) x = -2 * 1 * Family.palinstrophy two x + 2 * 1 * x 0 :=
  Family.enstrophy_identity 1 1 two two_nonzero 0 x

example (x : Point 3) :
    2 * (1 / 3) * (2 ^ 2 / (4 * (1 / 3) ^ 2) - Family.enstrophy x) -
        Family.zrate (Family.field (1 / 3) 2 pair 1) x =
      2 * (1 / 3) * ∑ i ∈ Finset.univ.erase 1, ((Family.lam (pair i) : ℝ) - 1) * x i ^ 2 +
        2 * (1 / 3) * (x 1 - 2 / (2 * (1 / 3))) ^ 2 :=
  Family.enstrophy_certificate (1 / 3) 2 (by norm_num) pair pair_nonzero 1 rfl x

/-- Enstrophy trapping for the 2-mode member at level `1 > f²/(4ν²) = 1/4`: the
level does not depend on the modes. -/
example (time : TimeDomain) (x₀ : Point 2) (initial : Family.enstrophy x₀ ≤ 1) :
    (∃ state, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ state) ∧
    (∀ x y : Signal 2, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ x →
      Nonlinear.Solves (Family.field 1 1 two 0) time x₀ y → Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (Family.field 1 1 two 0) time x₀ state →
      ∀ t ∈ time.domain, Family.enstrophy (state t) ≤ 1) :=
  Family.trapped_enstrophy 1 1 (by norm_num) two two_nonzero 0 rfl 1 (by norm_num) time x₀ initial

/-- Every mode is bounded by the enstrophy: `a_i² ≤ Z`. -/
example (x : Point 3) (i : Fin 3) : x i ^ 2 ≤ Family.enstrophy x :=
  Family.mode_sq_le_enstrophy x i

/-! ### The unforced energy and the laminar line -/

/-- The unforced energy identity on the `±` member: only the forced mode's cubic
term feeds `E_rest`. -/
example (x : Point 3) :
    Family.restRate pair 1 (Family.field (1 / 3) 2 pair 1) x =
      -2 * (1 / 3) * Family.restEnstrophy 1 x - x 1 * Family.forcedCubic pair 1 x :=
  Family.rest_identity (1 / 3) 2 pair pair_nonzero 1 rfl x

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

/-- `Z'` at `(1, 2, 3)` with `ν = 1`, `f = 1`: `−2·(1 + 8 + 45) + 2·2 = −104`, directly
from the field, and the same through the enstrophy identity. -/
example : Family.zrate (Family.field 1 1 triad 1) ![1, 2, 3] = -104 := by
  simp [Family.zrate, Family.field, Family.coefficient, Family.S, Family.cross, Family.lam,
    Fin.sum_univ_succ, triad]
  norm_num

example : Family.zrate (Family.field 1 1 triad 1) ![1, 2, 3] = -104 := by
  rw [Family.enstrophy_identity 1 1 triad (by decide) 1]
  simp [Family.palinstrophy, Family.lam, Fin.sum_univ_succ, triad]
  norm_num

/-- `λ(k forced) = 2` is what the identity uses: forcing `(1, 0)` instead, the
forcing enters `E'` as `2 f a_forced / λ = 2 f a_forced`, so the right-hand side
`−2νZ + f a_forced` is off by `f a_forced` at `(1, 2, 3)`. -/
example : Family.rate triad (Family.field 1 1 triad 0) ![1, 2, 3] ≠
    -2 * 1 * Family.enstrophy ![1, 2, 3] + 1 * (![1, 2, 3] : Point 3) 0 := by
  simp [Family.rate, Family.field, Family.coefficient, Family.S, Family.cross, Family.lam,
    Family.enstrophy, Fin.sum_univ_succ, triad]
  norm_num

/-! ### The laminar line on T3's modes -/

/-- T3's forced-mode coupling sum by hand: the pair `{(1,0), (2,1)}` couples to
`(1,1)` with `c((1,0),(2,1),(1,1)) = 1/2` and `c((2,1),(1,0),(1,1)) = −1/10`, so the
symmetric coefficient is `1/5` on each order and `K = 2/5`. -/
example : Family.couplingSum triad 1 = 2 / 5 := by
  simp only [Family.couplingSum, Family.symCoefficient, Fin.sum_univ_succ, Fin.sum_univ_zero, triad]
  simp [Family.coefficient, Family.S, Family.cross, Family.lam]
  norm_num

/-- Laminar attraction for T3's modes at `ν = 1/2`, `f = 1`, on the ball `Z ≤ 4`:
`γ = 2ν − K r = 1 − (2/5)·2 = 1/5`, and the unforced energy decays at that rate. -/
example (time : TimeDomain) (x₀ : Point 3) (initial : Family.enstrophy x₀ ≤ 2 ^ 2)
    (state : Signal 3) (h : Nonlinear.Solves (Family.field (1 / 2) 1 triad 1) time x₀ state) :
    ∀ t ∈ time.domain, Family.restEnergy triad 1 (state t) ≤
      Family.restEnergy triad 1 x₀ *
        Real.exp (-(2 * (1 / 2) - Family.couplingSum triad 1 * 2) * (t - time.start)) := by
  have K : Family.couplingSum triad 1 = 2 / 5 := by
    simp only [Family.couplingSum, Family.symCoefficient, Fin.sum_univ_succ, Fin.sum_univ_zero,
      triad]
    simp [Family.coefficient, Family.S, Family.cross, Family.lam]
    norm_num
  intro t ht
  exact ((Family.laminar_attracts (1 / 2) 1 (by norm_num) triad (by decide) 1 rfl 2
    (by norm_num) (by norm_num) (by rw [K]; norm_num) time x₀ initial).2.2 state h t ht).2

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

example : @Examples.GalerkinNS.K5.decreaseZ = @Examples.GalerkinNS.K5.decreaseZ_family := rfl

example (x : Point 12) :
    Examples.GalerkinNS.B2.trappingZ.rate (Nonlinear.field Examples.GalerkinNS.B2.compiled) x ≤
      Examples.GalerkinNS.B2.trappingZ.alpha *
        (Examples.GalerkinNS.B2.trappingZ.inner - Examples.GalerkinNS.B2.trappingZ.energy x) :=
  Examples.GalerkinNS.B2.decreaseZ_family x

/-- The energy weights themselves are a combination of `1/λ` and `1`, as
`only_two_diagonal` says of every lossless weighting of T3. -/
example : ∃ α β : ℝ, (1 : ℝ) = α * (1 / 1) + β ∧ (1 / 2 : ℝ) = α * (1 / 2) + β ∧
    (1 / 5 : ℝ) = α * (1 / 5) + β :=
  Examples.GalerkinNS.T3.only_two_diagonal ![1, 1 / 2, 1 / 5] (by simp [Matrix.cons_val]; norm_num)

/-- And a weighting that is not lossless for T3's triad is not a solution: the
hypothesis fails for `(1, 1, 0)`. -/
example : ¬ ((1 : ℝ) * (-3 / 20) + 1 * (2 / 5) + 0 * (-1 / 4) = 0) := by norm_num

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
info: 'Gimle.Forseti.GalerkinNS.Family.enstrophy_antisymm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.enstrophy_antisymm

/--
info: 'Gimle.Forseti.GalerkinNS.Family.cubic_enstrophy_flux_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.cubic_enstrophy_flux_zero

/--
info: 'Gimle.Forseti.GalerkinNS.Family.enstrophy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.enstrophy_identity

/--
info: 'Gimle.Forseti.GalerkinNS.Family.enstrophy_certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.enstrophy_certificate

/--
info: 'Gimle.Forseti.GalerkinNS.Family.trapped_enstrophy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.trapped_enstrophy

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

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.enstrophy_identity

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.only_two_diagonal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.only_two_diagonal

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.decreaseZ_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.decreaseZ_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.enstrophy_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.enstrophy_identity

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.only_two_diagonal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.only_two_diagonal

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.decreaseZ_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.decreaseZ_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.enstrophy_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.enstrophy_identity

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.only_two_diagonal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.only_two_diagonal

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.decreaseZ_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.decreaseZ_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.B2.enstrophy_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.symmetric_invariant_0'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.symmetric_invariant_0

/--
info: 'Gimle.Forseti.GalerkinNS.Family.rest_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.rest_identity

/--
info: 'Gimle.Forseti.GalerkinNS.Family.abs_forcedCubic_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.abs_forcedCubic_le

/--
info: 'Gimle.Forseti.GalerkinNS.Family.rest_decay'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.rest_decay

/--
info: 'Gimle.Forseti.GalerkinNS.Family.laminar_attracts'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Family.laminar_attracts

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.field_eq_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.field_eq_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.decrease_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.decrease_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.enstrophy_identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.enstrophy_identity

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.only_two_diagonal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.only_two_diagonal

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.decreaseZ_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.decreaseZ_family

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.enstrophy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.enstrophy_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.energy_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.gamma_pos'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.gamma_pos

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.couplingSum_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.couplingSum_eq

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.rest_decays'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.rest_decays

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3S.rest_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3S.rest_contract

end Gimle.Forseti.Tests.GalerkinNSFamily
