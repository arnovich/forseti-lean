import Gimle.Forseti.Nonlinear

/-! # The Galerkin Navier–Stokes family: energy identity, certificate, trapping

`Examples/GalerkinNS/{T3,K5,B2}.lean` prove, member by member and by `ring`,
that a Galerkin truncation of 2D incompressible Navier–Stokes (vorticity form
on the 2π-periodic square, cosine modes, forced in `cos(x + y)`) has the energy
identity `E' = −2νZ + f a₍₁,₁₎` and the sum-of-squares certificate
`2ν(f²/(8ν²) − E) − E' = ν(a₍₁,₁₎ − f/(2ν))² + 2ν Σ_{k ≠ (1,1)} (1 − 1/λ_k) a_k²`.
This module proves them once, for **every** member: any `n`, any modes
`k : Fin n → ℤ × ℤ` that are all nonzero, and any index `forced` with
`k forced = (1, 1)`.

The member with modes `k`, viscosity `ν` and forcing `f` is the field

    a_i' = −ν λ(k i) a_i + f [i = forced] + Σ_{j, l} c(k j, k l, k i) a_j a_l,

`λ(p) = |p|²`, over **ordered** pairs `(j, l)`, with the coupling

    c(p, q, k) = (p × q) / (2 λ_p) · ([p − q = ±k] − [p + q = ±k]),

which is the coefficient of `a_p a_q` in the projection `(1/2π²) ∫∫ · cos(k·x)`
of `−J(ψ, ω)` with `ω = Σ a_q cos(q·x)` and `Δψ = ω`, so `ψ = −Σ (a_p/λ_p) cos(p·x)`
(a paper derivation, checked by direct integration against `T3` and `K5` with
sympy outside this repository; not a Lean statement. What is checked here is
that each generated member's triad field is this coupling summed over both
orders: `tools/galerkin_ns.py` asserts it with exact rationals and each member
proves `field_eq_family`). Cosine modes span the even subspace, which the
vorticity equation preserves, so cosine-only truncations are genuine Galerkin
truncations. The generated members' triad coefficients are
this coupling summed over the two orders of each pair; each member states and
proves `field_eq_family`.

The cubic energy flux `Σ_{i,j,l} (2/λ(k i)) a_i c(k j, k l, k i) a_j a_l`
vanishes because exchanging the ψ-index `j` and the energy index `i` flips the
summand's sign, `(k × q) S(k, q, p) = −(p × q) S(p, q, k)` (`energy_antisymm`),
a finite-sum identity closed by `Finset.sum_comm` (`cubic_flux_zero`). The
identity and the certificate are algebra from it, using `λ(1, 1) = 2`. The
trapping then comes from `Nonlinear.lean`'s field-generic theorem, given
`ContDiff ℝ 1` of the field (`contDiff_field`, a finite sum of polynomials).

The derivation assumes the modes are pairwise distinct up to sign, so that
`a_i'` is the coefficient of `cos(k_i·x)`; the half-plane convention only fixes
a representative, and the coupling is even in each argument, so the choice does
not change the field. This is not a hypothesis of any theorem here: a duplicated
mode, or a mode and its negative, gives a field the theorems still cover — but
one whose triad terms are doubled relative to the PDE's projection. Nothing is
claimed about the PDE. -/

namespace Gimle.Forseti.GalerkinNS.Family

open Gimle.Forseti
open Gimle.Asgard
open Gimle.Asgard.Dynamics

/-- An integer wavevector. -/
abbrev Wave := ℤ × ℤ

/-- `λ(k) = |k|²`, the eigenvalue of `−Δ` on `cos(k·x)`. -/
def lam (k : Wave) : ℤ := k.1 ^ 2 + k.2 ^ 2

/-- The planar cross product `p × q`. -/
def cross (p q : Wave) : ℤ := p.1 * q.2 - p.2 * q.1

/-- `[p − q = ±k] − [p + q = ±k]`: how `2 sin(p·x) sin(q·x) = cos((p − q)·x) − cos((p + q)·x)`
lands on `cos(k·x)`. -/
def S (p q k : Wave) : ℤ :=
  (if p - q = k ∨ p - q = -k then 1 else 0) - (if p + q = k ∨ p + q = -k then 1 else 0)

/-- The ordered-pair coupling: the coefficient of `a_p a_q` in `a_k'`. -/
noncomputable def coefficient (p q k : Wave) : ℝ :=
  (cross p q : ℝ) / (2 * lam p) * S p q k

variable {n : ℕ}

/-- The member with modes `k`, viscosity `ν`, and forcing `f` on mode `forced`:
`a_i' = −ν λ(k i) a_i + f [i = forced] + Σ_{j, l} c(k j, k l, k i) a_j a_l`. -/
noncomputable def field (ν f : ℝ) (k : Fin n → Wave) (forced : Fin n) (x : Point n) :
    Point n :=
  fun i => -ν * lam (k i) * x i + (if i = forced then f else 0) +
    ∑ j, ∑ l, coefficient (k j) (k l) (k i) * x j * x l

/-- The energy `E = Σ a_i² / λ(k i)`. -/
noncomputable def energy (k : Fin n → Wave) (x : Point n) : ℝ := ∑ i, x i ^ 2 / lam (k i)

/-- The enstrophy `Z = Σ a_i²`. -/
noncomputable def enstrophy (x : Point n) : ℝ := ∑ i, x i ^ 2

/-- `E'` along a field: `Σ 2 a_i F_i(a) / λ(k i)`. -/
noncomputable def rate (k : Fin n → Wave) (F : Point n → Point n) (x : Point n) : ℝ :=
  ∑ i, 2 * x i / lam (k i) * F x i

/-! ## The coupling's combinatorics -/

theorem lam_pos {k : Wave} (hk : k ≠ 0) : 0 < lam k := by
  obtain ⟨k1, k2⟩ := k
  simp only [ne_eq, Prod.mk_eq_zero, not_and_or] at hk
  unfold lam
  rcases hk with h | h <;> positivity

theorem one_le_lam {k : Wave} (hk : k ≠ 0) : 1 ≤ lam k := lam_pos hk

@[simp] theorem lam_one_one : lam (1, 1) = 2 := rfl

/-- For nonzero `p, q` the two relations exclude each other, so `S` is `1`, `-1`
or `0` according to which (if any) holds. -/
theorem S_spec (p q k : Wave) (hp : p ≠ 0) (hq : q ≠ 0) :
    ((p - q = k ∨ p - q = -k) ∧ S p q k = 1) ∨
    ((p + q = k ∨ p + q = -k) ∧ S p q k = -1) ∨
    (¬(p - q = k ∨ p - q = -k) ∧ ¬(p + q = k ∨ p + q = -k) ∧ S p q k = 0) := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
  split_ifs with hA hB <;> omega

/-- When neither relation holds for `(p, q, k)`, neither holds after exchanging
`p` and `k`: `S k q p = 0`. -/
theorem S_swap_of_none (p q k : Wave)
    (hA : ¬(p - q = k ∨ p - q = -k)) (hB : ¬(p + q = k ∨ p + q = -k)) : S k q p = 0 := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_neg, Prod.snd_neg, not_or, not_and_or] at *
  split_ifs <;> omega

/-- Energy antisymmetry: exchanging the ψ-index and the energy index flips the
sign, `(k × q) S(k, q, p) = −(p × q) S(p, q, k)`; the discrete form of
`∫ ψ J(ψ, ω) = 0`. -/
theorem energy_antisymm (k p q : Wave) (hk : k ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    cross k q * S k q p = -(cross p q * S p q k) := by
  rcases S_spec p q k hp hq with ⟨hA, hS⟩ | ⟨hB, hS⟩ | ⟨hA, hB, hS⟩
  · rw [hS]
    rcases hA with h | h
    · subst h
      have v : S (p - q) q p = -1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [v]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]
      ring
    · have hk' : k = q - p := by rw [← neg_neg k, ← h, neg_sub]
      subst hk'
      have v : S (q - p) q p = 1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [v]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]
      ring
  · rw [hS]
    rcases hB with h | h
    · subst h
      have v : S (p + q) q p = 1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [v]
      simp only [cross, Prod.fst_add, Prod.snd_add]
      ring
    · have hk' : k = -(p + q) := by rw [h, neg_neg]
      subst hk'
      have v : S (-(p + q)) q p = -1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [v]
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      ring
  · rw [hS, S_swap_of_none p q k hA hB]
    ring

/-- The cubic energy flux `Σ_{i,j,l} (2/λ(k i)) a_i c(k j, k l, k i) a_j a_l`
vanishes for every finite list of nonzero wavevectors: exchanging `i` and `j`
flips the summand's sign, so the sum equals its own negative. -/
theorem cubic_flux_zero (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (a : Point n) :
    ∑ i, ∑ j, ∑ l, (2 / lam (k i) : ℝ) * a i * (coefficient (k j) (k l) (k i) * a j * a l)
      = 0 := by
  set g : Fin n → Fin n → Fin n → ℝ := fun i j l =>
    (2 / lam (k i) : ℝ) * a i * (coefficient (k j) (k l) (k i) * a j * a l) with hg
  have flip : ∀ i j l, g j i l = -g i j l := by
    intro i j l
    have key := energy_antisymm (k i) (k j) (k l) (hk i) (hk j) (hk l)
    have key' : (cross (k i) (k l) : ℝ) * S (k i) (k l) (k j) =
        -((cross (k j) (k l) : ℝ) * S (k j) (k l) (k i)) := by exact_mod_cast key
    have hi' : (lam (k i) : ℝ) ≠ 0 := by exact_mod_cast (lam_pos (hk i)).ne'
    have hj' : (lam (k j) : ℝ) ≠ 0 := by exact_mod_cast (lam_pos (hk j)).ne'
    simp only [hg, coefficient]
    field_simp
    linear_combination (a i * a j * a l) * key'
  have swap : ∑ i, ∑ j, ∑ l, g i j l = -∑ i, ∑ j, ∑ l, g i j l := by
    calc ∑ i, ∑ j, ∑ l, g i j l = ∑ j, ∑ i, ∑ l, g i j l := Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ l, -g j i l := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun l _ => flip j i l
      _ = -∑ i, ∑ j, ∑ l, g i j l := by simp only [Finset.sum_neg_distrib]
  linarith

/-! ## The energy identity and the certificate -/

/-- One term of `E'`: the dissipation and forcing part, and the cubic part. -/
theorem rate_expand (ν f : ℝ) (k : Fin n → Wave) (forced : Fin n) (x : Point n) :
    rate k (field ν f k forced) x =
      ∑ i, 2 * x i / lam (k i) * (-ν * lam (k i) * x i + (if i = forced then f else 0)) +
        ∑ i, ∑ j, ∑ l, (2 / lam (k i) : ℝ) * x i *
          (coefficient (k j) (k l) (k i) * x j * x l) := by
  rw [rate, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [field, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The energy identity**, for every member: `E' = −2νZ + f a_forced` when the
modes are nonzero and `k forced = (1, 1)`; `(1, 1)` enters only through `λ = 2`. -/
theorem energy_identity (ν f : ℝ) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (x : Point n) :
    rate k (field ν f k forced) x = -2 * ν * enstrophy x + f * x forced := by
  rw [rate_expand, cubic_flux_zero k hk x, add_zero]
  have each : ∀ i, 2 * x i / lam (k i) * (-ν * lam (k i) * x i + (if i = forced then f else 0)) =
      -2 * ν * x i ^ 2 + (if i = forced then f * x i else 0) := by
    intro i
    have hi : (lam (k i) : ℝ) ≠ 0 := by exact_mod_cast (lam_pos (hk i)).ne'
    split_ifs with h
    · subst h
      rw [hf, lam_one_one]
      push_cast
      ring
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun i _ => each i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), enstrophy, Finset.mul_sum]

/-- **The certificate**, for every member: `2ν(f²/(8ν²) − E) − E'` is the sum of
squares `ν(a_forced − f/(2ν))² + 2ν Σ_{i ≠ forced} (1 − 1/λ(k i)) a_i²`, with
nonnegative weights since `λ ≥ 1` on nonzero modes. -/
theorem certificate (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (x : Point n) :
    2 * ν * (f ^ 2 / (8 * ν ^ 2) - energy k x) - rate k (field ν f k forced) x =
      ν * (x forced - f / (2 * ν)) ^ 2 +
        2 * ν * ∑ i ∈ Finset.univ.erase forced, (1 - 1 / lam (k i)) * x i ^ 2 := by
  rw [energy_identity ν f k hk forced hf x, energy, enstrophy,
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2 / (lam (k i) : ℝ))
      (Finset.mem_univ forced),
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ forced), hf, lam_one_one]
  have split : ∑ i ∈ Finset.univ.erase forced, (1 - 1 / (lam (k i) : ℝ)) * x i ^ 2 =
      ∑ i ∈ Finset.univ.erase forced, x i ^ 2 -
        ∑ i ∈ Finset.univ.erase forced, x i ^ 2 / (lam (k i) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [split]
  push_cast
  field_simp
  ring

/-- The squares are nonnegative, so `E' ≤ 2ν(f²/(8ν²) − E)` at every state. -/
theorem decrease_rate (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (x : Point n) :
    rate k (field ν f k forced) x ≤ 2 * ν * (f ^ 2 / (8 * ν ^ 2) - energy k x) := by
  have h := certificate ν f hν k hk forced hf x
  have squares : 0 ≤ ∑ i ∈ Finset.univ.erase forced, (1 - 1 / (lam (k i) : ℝ)) * x i ^ 2 := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr ?_) (sq_nonneg _)
    exact div_le_one_of_le₀ (by exact_mod_cast one_le_lam (hk i))
      (by exact_mod_cast (lam_pos (hk i)).le)
  nlinarith [mul_nonneg hν.le (sq_nonneg (x forced - f / (2 * ν))), mul_nonneg hν.le squares]

/-! ## The field is smooth -/

/-- The field is a finite sum of polynomials in the state, hence `C¹`. -/
theorem contDiff_field (ν f : ℝ) (k : Fin n → Wave) (forced : Fin n) :
    ContDiff ℝ 1 (field ν f k forced) := by
  refine contDiff_pi.mpr fun i => ?_
  simp only [field]
  refine ((contDiff_const.mul (contDiff_apply ℝ ℝ i)).add contDiff_const).add ?_
  refine ContDiff.sum fun j _ => ContDiff.sum fun l _ => ?_
  exact (contDiff_const.mul (contDiff_apply ℝ ℝ j)).mul (contDiff_apply ℝ ℝ l)

/-! ## The trapping, from `Nonlinear.lean` -/

/-- The family's `Trapping`: weights `1/λ(k i)`, centre `0`, `α = 2ν`, inner level
`f²/(8ν²)`, any trapped level `C > f²/(8ν²)`, and sup-norm radius
`1 + C Σ λ(k i)`, which covers `{E ≤ C}` since `C λ_i ≤ C Σ λ ≤ (1 + C Σ λ)²`. -/
noncomputable def trapping (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C) : Nonlinear.Trapping n where
  weights := fun i => 1 / lam (k i)
  centre := fun _ => 0
  alpha := 2 * ν
  inner := f ^ 2 / (8 * ν ^ 2)
  bound := C
  radius := 1 + C * ∑ i, (lam (k i) : ℝ)
  weights_pos := fun i => one_div_pos.mpr (by exact_mod_cast lam_pos (hk i))
  alpha_pos := by linarith
  margin := hC
  radius_nonneg := by
    have hC0 : 0 ≤ C := le_trans (by positivity) hC.le
    have hs : 0 ≤ ∑ i, (lam (k i) : ℝ) :=
      Finset.sum_nonneg fun i _ => by exact_mod_cast (lam_pos (hk i)).le
    exact add_nonneg zero_le_one (mul_nonneg hC0 hs)
  covers := fun i => by
    have hlam : (0 : ℝ) < lam (k i) := by exact_mod_cast lam_pos (hk i)
    have hC0 : 0 ≤ C := le_trans (by positivity) hC.le
    have hs : 0 ≤ ∑ j, (lam (k j) : ℝ) :=
      Finset.sum_nonneg fun j _ => by exact_mod_cast (lam_pos (hk j)).le
    have hle : (lam (k i) : ℝ) ≤ ∑ j, (lam (k j) : ℝ) :=
      Finset.single_le_sum (f := fun j => (lam (k j) : ℝ))
        (fun j _ => by exact_mod_cast (lam_pos (hk j)).le) (Finset.mem_univ i)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlam]
    nlinarith [mul_le_mul_of_nonneg_left hle hC0, sq_nonneg (C * ∑ j, (lam (k j) : ℝ)),
      mul_nonneg hC0 hs]

/-- The family `Trapping`'s `energy` is `energy k`. -/
theorem trapping_energy (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C) (x : Point n) :
    (trapping ν f hν k hk C hC).energy x = energy k x := by
  simp only [Nonlinear.Trapping.energy, trapping, energy]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The family `Trapping`'s `rate` is `rate k`. -/
theorem trapping_rate (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C) (F : Point n → Point n) (x : Point n) :
    (trapping ν f hν k hk C hC).rate F x = rate k F x := by
  simp only [Nonlinear.Trapping.rate, trapping, rate]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The differential inequality in the shape `Nonlinear.Trapping` consumes. -/
theorem decrease (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C)
    (x : Point n) :
    (trapping ν f hν k hk C hC).rate (field ν f k forced) x ≤
      (trapping ν f hν k hk C hC).alpha *
        ((trapping ν f hν k hk C hC).inner - (trapping ν f hν k hk C hC).energy x) := by
  rw [trapping_rate, trapping_energy]
  exact decrease_rate ν f hν k hk forced hf x

/-- A forward solution from any start with `E ≤ C` exists for all `t ≥ start`. -/
theorem exists_solution (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : energy k x₀ ≤ C) :
    ∃ state, Nonlinear.Solves (field ν f k forced) time x₀ state :=
  (trapping ν f hν k hk C hC).exists_solution _ (contDiff_field ν f k forced)
    (decrease ν f hν k hk forced hf C hC) time x₀ (by rwa [trapping_energy])

/-- Two forward solutions from the same such start agree on the whole domain. -/
theorem unique (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : energy k x₀ ≤ C)
    {x y : Signal n} (hx : Nonlinear.Solves (field ν f k forced) time x₀ x)
    (hy : Nonlinear.Solves (field ν f k forced) time x₀ y) : Set.EqOn x y time.domain :=
  (trapping ν f hν k hk C hC).unique _ (contDiff_field ν f k forced)
    (decrease ν f hν k hk forced hf C hC) time x₀ (by rwa [trapping_energy]) hx hy

/-- Every forward solution from such a start keeps `E ≤ C`. -/
theorem invariant (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : energy k x₀ ≤ C)
    (state : Signal n) (h : Nonlinear.Solves (field ν f k forced) time x₀ state) :
    ∀ t ∈ time.domain, energy k (state t) ≤ C := fun t ht => by
  have bound := (trapping ν f hν k hk C hC).invariant _ (decrease ν f hν k hk forced hf C hC)
    time x₀ (by rwa [trapping_energy]) state h t ht
  rwa [trapping_energy] at bound

/-- **Trapping, for every member**: from any start with `E ≤ C`, `C > f²/(8ν²)`, a
forward solution exists for all `t ≥ start`, it is unique, and it keeps `E ≤ C`. -/
theorem trapped (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (8 * ν ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : energy k x₀ ≤ C) :
    (∃ state, Nonlinear.Solves (field ν f k forced) time x₀ state) ∧
    (∀ x y : Signal n, Nonlinear.Solves (field ν f k forced) time x₀ x →
      Nonlinear.Solves (field ν f k forced) time x₀ y → Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (field ν f k forced) time x₀ state →
      ∀ t ∈ time.domain, energy k (state t) ≤ C) :=
  ⟨exists_solution ν f hν k hk forced hf C hC time x₀ initial,
    fun _ _ hx hy => unique ν f hν k hk forced hf C hC time x₀ initial hx hy,
    invariant ν f hν k hk forced hf C hC time x₀ initial⟩

#print axioms energy_antisymm
#print axioms cubic_flux_zero
#print axioms energy_identity
#print axioms certificate
#print axioms decrease
#print axioms contDiff_field
#print axioms exists_solution
#print axioms unique
#print axioms invariant
#print axioms trapped

end Gimle.Forseti.GalerkinNS.Family
