import Gimle.Forseti.StreamObservation
import Gimle.Forseti.FieldBound
import Gimle.Forseti.Examples.FormalHeatContract

/-! Coefficient observations of two stream circuits, proved by checked
certificates.

**A second derivative.** `∂²/∂x²` on axes `[t, x]` (OGF), observed on the output
window `x^0, x^1` at `t^0`. Asgard's lowering computes the dependency halo — the
input coefficients `u[t^0, x^2]` and `u[t^0, x^3]`, both *outside* the output
window — and `halo_changes_output` shows that changing one of them, with the
window unchanged, changes an observed coefficient. `space_nonneg` is a total
stream contract proved from a 017 certificate over those named inputs.

**The formal heat reconstruction.** Asgard's `FormalHeat.circuit` returns
`[u_xx, u]`, rebuilding `u` by integrating `u_xx` along `t` from a boundary
port. `heat_observed` proves, for every input admitted by task 018's
`FormalHeatContract.admitted` (the whole stream `u = x² + 2t` and the boundary
profile `x²`), that the observed output coefficients are those of `x² + 2t`:
`u[t^1, x^0] = 2`, `u[t^0, x^2] = 1` and `u_xx[t^0, x^0] = 2`. The leaf reads
only `u[t^0, x^2]` and `boundary[t^0, x^2]`; the full-stream precondition is
kept, and the leaf antecedent is proved from it.

**Refutation needs an admitted input.** `weak_leaf_refuted` refutes a leaf that
forgot the input hypothesis, yet `weak_root_holds` proves the root claim: the
counterexample cannot be extended to an admitted input. `altered_profile_refuted`
is a root refutation: an input with the altered initial profile `2x²`, admitted
by the altered precondition, whose observed `u[t^0, x^2]` is `2`, not `1`.

Everything here is about exact formal coefficients. The real field these
streams represent is `HeatFieldBound`'s, through asgard-lean 024.
-/

namespace Gimle.Forseti.Examples.StreamObservation

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Stream
open Gimle.Forseti.StreamObservation
open Gimle.Asgard
open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Lowering
open Gimle.Asgard.Examples.FormalHeat (heat boundary two circuit)

/-- The ordered axes `[t, x]`. -/
def axes : Fin 2 → String := !["t", "x"]

/-- A weight on a constant square: `w · 1²`. -/
def weight {k : Nat} (w : ℚ) : SquareSum k := ⟨[(w, .constant 1)]⟩

/-- An unused multiplier slot. -/
def unused {k : Nat} : SquareSum k := ⟨[]⟩

/-! ### A second derivative and its halo -/

/-- `∂²/∂x²`, as two derivative stages. -/
def secondDerivative : Streams.Circuit .ogf 2 1 1 :=
  .compose (.unary (.derivative 1)) (.unary (.derivative 1))

/-- The output window `x^0, x^1` at `t^0`. -/
def spaceOutput : Observation .ogf 2 1 :=
  .ofManifest ⟨axes, !["u_xx"], [⟨0, ![0, 0]⟩, ⟨0, ![0, 1]⟩]⟩

/-- Asgard's lowering of that observation. -/
def spaceLowered := lowered secondDerivative !["u"] spaceOutput.manifest (by decide +kernel)

/-- **The dependency halo**, computed by Asgard: two input coefficients, both
past the output window along `x`. -/
theorem space_halo : spaceLowered.inputs.slots = [⟨0, ![0, 2]⟩, ⟨0, ![0, 3]⟩] := by
  decide +kernel

/-- The input coefficients the lowering reads, named. -/
def spaceInput : Observation .ogf 2 1 := .ofManifest spaceLowered.inputs

example : spaceInput.context.names = ["u[t^0, x^2]", "u[t^0, x^3]"] := by decide +kernel

/-- `u[t^0, x^2] ≥ 0`. -/
def spaceAntecedent : Formula spaceInput.context.dimension :=
  .atom .ge (spaceInput.context.var "u[t^0, x^2]" (by decide +kernel))

/-- `u_xx[t^0, x^0] ≥ 0`. -/
def spacePost : Formula spaceOutput.context.dimension :=
  .atom .ge (spaceOutput.context.var "u_xx[t^0, x^0]" (by decide +kernel))

/-- `u[t^0, x^2] ≥ 0 ⊨ u_xx[t^0, x^0] ≥ 0`, over the named input coefficients. -/
def spaceGoal : Goal := leafGoal secondDerivative spaceInput spaceOutput spaceAntecedent spacePost

/-- `u_xx[t^0, x^0] = 2 · u[t^0, x^2]`: twice the antecedent. -/
def spaceCertificate : EntailmentCertificate spaceInput.context.dimension :=
  ⟨[⟨unused, [weight 2]⟩]⟩

/-- The full-stream precondition: `u`'s `x²` coefficient is nonnegative. -/
def spacePre : StreamPredicate 2 1 := fun x => 0 ≤ x 0 (Degrees.toIndex ![0, 2])

/-- **A total stream contract from a checked certificate.** -/
theorem space_nonneg :
    StreamHoare spacePre secondDerivative (spaceOutput.Observes spacePost) :=
  lift_certificate (lowered_ok _ _ _ _) spaceInput rfl (antecedent := spaceAntecedent)
    spaceCertificate (by decide +kernel)
    fun x admitted => by
      show 0 ≤ (spaceInput.context.var "u[t^0, x^2]" _).eval (spaceInput.point x)
      rw [spaceInput.var_eval (by decide +kernel : spaceInput.slot _ = ⟨0, ![0, 2]⟩)]
      exact_mod_cast admitted

/-- The stream with a single coefficient `1` at `u[t^0, x^2]`. -/
noncomputable def bump : Stream 2 := fun k => if k = Degrees.toIndex ![0, 2] then 1 else 0

/-- **A coefficient outside the output window changes an observed result.** The
zero stream and `bump` agree on the whole output window `t^0, x^0..1`, but their
observed `u_xx[t^0, x^0]` are `0` and `2`. -/
theorem halo_changes_output :
    Window ![1, 2] 0 (0 : Stream 2) ![bump] ∧
      (secondDerivative.value ![0]) 0 (Degrees.toIndex ![0, 0]) = 0 ∧
      (secondDerivative.value ![bump]) 0 (Degrees.toIndex ![0, 0]) = 2 := by
  have term : lowerRaw secondDerivative 0 ![0, 0] =
      .mul (.const 1) (.mul (.const 2) (.slot ⟨0, ![0, 2]⟩)) := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · unfold Window truncate
    funext k
    by_cases below : ∀ i, k i < (![1, 2] : Fin 2 → ℕ) i
    · have outside : k ≠ Degrees.toIndex ![0, 2] := by
        rintro rfl
        simpa using below 1
      simp only [below, Matrix.cons_val_fin_one, bump, outside, if_false]
      rfl
    · simp [below]
  · rw [lowerRaw_correct _ rfl, term]
    simp only [Term.eval]
    show (1 : ℚ) * (2 * 0) = 0
    norm_num
  · rw [lowerRaw_correct _ rfl, term]
    simp [Term.eval, bump]

/-! ### The formal heat reconstruction -/

/-- `u[t^1, x^0]` and `u[t^0, x^2]` of the rebuilt `u`, and `u_xx[t^0, x^0]`. -/
def heatOutput : Observation .ogf 2 2 :=
  .ofManifest ⟨axes, !["u_xx", "u"], [⟨1, ![1, 0]⟩, ⟨1, ![0, 2]⟩, ⟨0, ![0, 0]⟩]⟩

/-- Asgard's lowering of the heat observation, on the circuit's own inputs. -/
def heatLowered :=
  lowered circuit !["u", "boundary", "unused"] heatOutput.manifest (by decide +kernel)

/-- The halo: the boundary's `x²` coefficient and `u`'s. Nothing is read from
the unused port. -/
theorem heat_halo : heatLowered.inputs.slots = [⟨1, ![0, 2]⟩, ⟨0, ![0, 2]⟩] := by
  decide +kernel

/-- The heat input coefficients, named. -/
def heatInput : Observation .ogf 2 3 := .ofManifest heatLowered.inputs

example : heatInput.context.names = ["boundary[t^0, x^2]", "u[t^0, x^2]"] := by decide +kernel

/-- `u[t^0, x^2]`. -/
abbrev inU : Polynomial.Expr heatInput.context.dimension :=
  heatInput.context.var "u[t^0, x^2]" (by decide +kernel)
/-- `boundary[t^0, x^2]`. -/
abbrev inBoundary : Polynomial.Expr heatInput.context.dimension :=
  heatInput.context.var "boundary[t^0, x^2]" (by decide +kernel)
/-- Output `u[t^1, x^0]`. -/
abbrev outTime : Polynomial.Expr heatOutput.context.dimension :=
  heatOutput.context.var "u[t^1, x^0]" (by decide +kernel)
/-- Output `u[t^0, x^2]`. -/
abbrev outSpace : Polynomial.Expr heatOutput.context.dimension :=
  heatOutput.context.var "u[t^0, x^2]" (by decide +kernel)
/-- Output `u_xx[t^0, x^0]`. -/
abbrev outRhs : Polynomial.Expr heatOutput.context.dimension :=
  heatOutput.context.var "u_xx[t^0, x^0]" (by decide +kernel)

/-- `p = q`, as the two non-strict constraints the certificate checker reads. -/
def equals {k : Nat} (p q : Polynomial.Expr k) : Formula k :=
  (Formula.atom .ge (p - q)).and (.atom .le (p - q))

/-- The leaf antecedent: the two `x²` coefficients are `1`. -/
def heatAntecedent : Formula heatInput.context.dimension :=
  (equals inU 1).and (equals inBoundary 1)

/-- The observed claim: the coefficients of `x² + 2t` and of `u_xx = 2`. -/
def heatPost : Formula heatOutput.context.dimension :=
  (equals outTime 2).and ((equals outSpace 1).and (equals outRhs 2))

/-- The leaf goal the lowering poses. -/
def heatGoal : Goal := leafGoal circuit heatInput heatOutput heatAntecedent heatPost

/-- Each consequent constraint is a constant multiple of one antecedent
constraint: `u[t^1] = u_xx = 2·u[x²]` and the rebuilt `x²` coefficient is the
boundary's. Antecedent order: `u ≥ 1, u ≤ 1, boundary ≥ 1, boundary ≤ 1`. -/
def heatCertificate : EntailmentCertificate heatInput.context.dimension :=
  ⟨[⟨unused, [weight 2, unused, unused, unused]⟩, ⟨unused, [unused, weight 2, unused, unused]⟩,
    ⟨unused, [unused, unused, weight 1, unused]⟩, ⟨unused, [unused, unused, unused, weight 1]⟩,
    ⟨unused, [weight 2, unused, unused, unused]⟩, ⟨unused, [unused, weight 2, unused, unused]⟩]⟩

theorem heatCertificate_checks : heatCertificate.check heatGoal = true := by decide +kernel

/-- The `x²` coefficient of every admitted input's `u` and boundary port is `1`. -/
theorem heat_inputs (x : StreamPoint 2 3) (admitted : FormalHeatContract.admitted x) :
    heatAntecedent.holds (heatInput.point x) := by
  obtain ⟨u, profile⟩ := admitted
  have atU : (x 0 (Degrees.toIndex ![0, 2]) : ℝ) = 1 := by
    rw [u]; norm_num [heat]
  have atBoundary : (x 1 (Degrees.toIndex ![0, 2]) : ℝ) = 1 := by
    rw [profile _ (by simp)]; norm_num [boundary]
  have eu := heatInput.var_eval (name := "u[t^0, x^2]") (found := by decide +kernel)
    (by decide +kernel : heatInput.slot _ = ⟨0, ![0, 2]⟩) x
  have eb := heatInput.var_eval (name := "boundary[t^0, x^2]") (found := by decide +kernel)
    (by decide +kernel : heatInput.slot _ = ⟨1, ![0, 2]⟩) x
  rw [atU] at eu
  rw [atBoundary] at eb
  simp only [heatAntecedent, equals, inU, inBoundary, Formula.holds, Relation.holds,
    eval_sub, eval_ofNat, eu, eb]
  norm_num

/-- **The heat circuit's observed output is that of `x² + 2t`**, for every input
task 018 admits: a total stream contract over the original circuit, from a
certificate over two named input coefficients. -/
theorem heat_observed :
    StreamHoare FormalHeatContract.admitted circuit (heatOutput.Observes heatPost) :=
  lift_certificate (lowered_ok _ _ _ _) heatInput rfl heatCertificate heatCertificate_checks
    heat_inputs

/-! ### Refutation needs an admitted input -/

/-- A leaf without the input hypothesis: `tru ⊨ u[t^1, x^0] ≥ 0`. -/
def weakGoal : Goal :=
  leafGoal circuit heatInput heatOutput .tru (.atom .ge outTime)

/-- The leaf is refuted by a coefficient witness with `u[t^0, x^2] = -1`… -/
theorem weak_leaf_refuted : ¬ weakGoal.Entailment :=
  refutes_sound weakGoal [("boundary[t^0, x^2]", 0), ("u[t^0, x^2]", -1)] (by decide +kernel)

/-- …but no admitted input has that coefficient, and the root claim holds: its
leaf, with the input hypothesis, is certified. No root refutation exists. -/
theorem weak_root_holds :
    StreamHoare FormalHeatContract.admitted circuit
      (heatOutput.Observes (.atom .ge outTime)) :=
  lift_certificate (lowered_ok _ _ _ _) heatInput rfl
    (antecedent := heatAntecedent) ⟨[⟨weight 2, [weight 2, unused, unused, unused]⟩]⟩
    (by decide +kernel) heat_inputs

/-- The altered initial profile `2x²`. -/
def alteredProfile : Stream 2 := fun k => if k 0 = 0 ∧ k 1 = 2 then 2 else 0

/-- The precondition with the altered profile. -/
def alteredAdmitted : StreamPredicate 2 3 :=
  fun x => x 0 = heat ∧ Boundary 0 1 alteredProfile x

/-- The unaltered claim `u[t^0, x^2] = 1`, from `u`'s coefficient alone. -/
def alteredGoal : Goal :=
  leafGoal circuit heatInput heatOutput (equals inU 1) (equals outSpace 1)

/-- The named witness: `u`'s coefficient is `1` and the boundary's is `2`. -/
def alteredAnswer : Syntax.Context.Assignment :=
  [("boundary[t^0, x^2]", 2), ("u[t^0, x^2]", 1)]

/-- **A root refutation.** The witness refutes the leaf, and extends to the full
input `[x² + 2t, 2x², 0]`, admitted by the altered precondition, whose observed
rebuilt `x²` coefficient is `2`. -/
theorem altered_profile_refuted :
    ¬ StreamHoare alteredAdmitted circuit (heatOutput.Observes (equals outSpace 1)) := by
  refine refutes_root (lowered_ok _ _ _ _) heatInput rfl (antecedent := equals inU 1)
    (answer := alteredAnswer) (by decide +kernel) ![heat, alteredProfile, 0]
    ⟨rfl, fun _ _ => rfl⟩ ?_
  intro i
  have values : ∀ i, (Syntax.Context.valueOf alteredAnswer (heatInput.context.name i)).getD 0 =
      ![2, 1] (Fin.cast (by decide +kernel) i) := by decide +kernel
  rw [values]
  fin_cases i
  · rw [heatInput.point_of_slot (by decide +kernel : heatInput.slot _ = ⟨1, ![0, 2]⟩)]
    norm_num [alteredProfile]
  · rw [heatInput.point_of_slot (by decide +kernel : heatInput.slot _ = ⟨0, ![0, 2]⟩)]
    norm_num [heat]

end Gimle.Forseti.Examples.StreamObservation
