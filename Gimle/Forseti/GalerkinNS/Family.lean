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

/-- The palinstrophy `P = Σ λ(k i) a_i²`, the enstrophy's dissipation. -/
noncomputable def palinstrophy (k : Fin n → Wave) (x : Point n) : ℝ := ∑ i, lam (k i) * x i ^ 2

/-- `Z'` along a field: `Σ 2 a_i F_i(a)`. -/
noncomputable def zrate (F : Point n → Point n) (x : Point n) : ℝ := ∑ i, 2 * x i * F x i

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

/-! ## The enstrophy's combinatorics -/

/-- When neither relation holds for `(p, q, k)`, neither holds for `(p, k, q)`:
`S p k q = 0`. -/
theorem S_exchange_of_none (p q k : Wave)
    (hA : ¬(p - q = k ∨ p - q = -k)) (hB : ¬(p + q = k ∨ p + q = -k)) : S p k q = 0 := by
  obtain ⟨k1, k2⟩ := k
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_neg, Prod.snd_neg, not_or, not_and_or] at *
  split_ifs <;> omega

/-- Enstrophy antisymmetry: exchanging the ω-index and the enstrophy index, the
ψ-index fixed, flips the sign: `(p × q) S(p, q, k) = −(p × k) S(p, k, q)`; the
discrete form of `∫ ω J(ψ, ω) = 0`. This is a different exchange from
`energy_antisymm`, and the weight `1/λ_p` is untouched by it. -/
theorem enstrophy_antisymm (p q k : Wave) (hp : p ≠ 0) (hq : q ≠ 0) (hk : k ≠ 0) :
    cross p q * S p q k = -(cross p k * S p k q) := by
  rcases S_spec p q k hp hq with ⟨hA, hS⟩ | ⟨hB, hS⟩ | ⟨hA, hB, hS⟩
  · rw [hS]
    rcases hA with h | h
    · subst h
      have w : S p (p - q) q = 1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [w]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]
      ring
    · have hk' : k = q - p := by rw [← neg_neg k, ← h, neg_sub]
      subst hk'
      have w : S p (q - p) q = -1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [w]
      simp only [cross, Prod.fst_sub, Prod.snd_sub]
      ring
  · rw [hS]
    rcases hB with h | h
    · subst h
      have w : S p (p + q) q = 1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [w]
      simp only [cross, Prod.fst_add, Prod.snd_add]
      ring
    · have hk' : k = -(p + q) := by rw [h, neg_neg]
      subst hk'
      have w : S p (-(p + q)) q = -1 := by
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only [S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at *
        split_ifs <;> omega
      rw [w]
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      ring
  · rw [hS, S_exchange_of_none p q k hA hB]
    ring

/-- The cubic enstrophy flux `Σ_{i,j,l} 2 a_i c(k j, k l, k i) a_j a_l` vanishes for
every finite list of nonzero wavevectors: exchanging `i` and `l` flips the
summand's sign, so the sum equals its own negative. -/
theorem cubic_enstrophy_flux_zero (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (a : Point n) :
    ∑ i, ∑ j, ∑ l, 2 * a i * (coefficient (k j) (k l) (k i) * a j * a l) = 0 := by
  set g : Fin n → Fin n → Fin n → ℝ := fun i j l =>
    2 * a i * (coefficient (k j) (k l) (k i) * a j * a l) with hg
  have flip : ∀ i j l, g l j i = -g i j l := by
    intro i j l
    have key := enstrophy_antisymm (k j) (k l) (k i) (hk j) (hk l) (hk i)
    have key' : (cross (k j) (k l) : ℝ) * S (k j) (k l) (k i) =
        -((cross (k j) (k i) : ℝ) * S (k j) (k i) (k l)) := by exact_mod_cast key
    have swapc : coefficient (k j) (k i) (k l) = -coefficient (k j) (k l) (k i) := by
      simp only [coefficient]
      linear_combination (1 / (2 * (lam (k j) : ℝ))) * key'
    simp only [hg, swapc]
    ring
  have inner : ∀ i, ∑ j, ∑ l, g i j l = ∑ l, ∑ j, g i j l := fun i => Finset.sum_comm
  have swap : ∑ i, ∑ j, ∑ l, g i j l = -∑ i, ∑ j, ∑ l, g i j l := by
    calc ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ l, ∑ j, g i j l :=
          Finset.sum_congr rfl fun i _ => inner i
      _ = ∑ l, ∑ i, ∑ j, g i j l := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, -g l j i := by
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          rw [flip l j i]
      _ = -∑ l, ∑ i, ∑ j, g l j i := by simp only [Finset.sum_neg_distrib]
      _ = -∑ i, ∑ j, ∑ l, g i j l := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          exact (inner l).symm
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

/-! ## The enstrophy identity and its certificate -/

/-- One term of `Z'`: the dissipation and forcing part, and the cubic part. -/
theorem zrate_expand (ν f : ℝ) (k : Fin n → Wave) (forced : Fin n) (x : Point n) :
    zrate (field ν f k forced) x =
      ∑ i, 2 * x i * (-ν * lam (k i) * x i + (if i = forced then f else 0)) +
        ∑ i, ∑ j, ∑ l, 2 * x i * (coefficient (k j) (k l) (k i) * x j * x l) := by
  rw [zrate, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [field, mul_add, Finset.mul_sum]

/-- **The enstrophy identity**, for every member: `Z' = −2νP + 2 f a_forced`, with
`P = Σ λ(k i) a_i²` the palinstrophy. -/
theorem enstrophy_identity (ν f : ℝ) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (x : Point n) :
    zrate (field ν f k forced) x = -2 * ν * palinstrophy k x + 2 * f * x forced := by
  rw [zrate_expand, cubic_enstrophy_flux_zero k hk x, add_zero]
  have each : ∀ i, 2 * x i * (-ν * lam (k i) * x i + (if i = forced then f else 0)) =
      -2 * ν * (lam (k i) * x i ^ 2) + (if i = forced then 2 * f * x i else 0) := by
    intro i
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => each i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), palinstrophy, Finset.mul_sum]

/-- **The enstrophy certificate**, for every member: `2ν(f²/(4ν²) − Z) − Z'` is the
sum of squares `2ν Σ_{i ≠ forced} (λ(k i) − 1) a_i² + 2ν (a_forced − f/(2ν))²`, with
nonnegative weights since `λ ≥ 1` on nonzero modes. -/
theorem enstrophy_certificate (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (x : Point n) :
    2 * ν * (f ^ 2 / (4 * ν ^ 2) - enstrophy x) - zrate (field ν f k forced) x =
      2 * ν * ∑ i ∈ Finset.univ.erase forced, ((lam (k i) : ℝ) - 1) * x i ^ 2 +
        2 * ν * (x forced - f / (2 * ν)) ^ 2 := by
  rw [enstrophy_identity ν f k hk forced x, enstrophy, palinstrophy,
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ forced),
    ← Finset.add_sum_erase Finset.univ (fun i => (lam (k i) : ℝ) * x i ^ 2)
      (Finset.mem_univ forced), hf, lam_one_one]
  have split : ∑ i ∈ Finset.univ.erase forced, ((lam (k i) : ℝ) - 1) * x i ^ 2 =
      ∑ i ∈ Finset.univ.erase forced, (lam (k i) : ℝ) * x i ^ 2 -
        ∑ i ∈ Finset.univ.erase forced, x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [split]
  push_cast
  field_simp
  ring

/-- The squares are nonnegative, so `Z' ≤ 2ν(f²/(4ν²) − Z)` at every state. -/
theorem enstrophy_decrease_rate (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave)
    (hk : ∀ i, k i ≠ 0) (forced : Fin n) (hf : k forced = (1, 1)) (x : Point n) :
    zrate (field ν f k forced) x ≤ 2 * ν * (f ^ 2 / (4 * ν ^ 2) - enstrophy x) := by
  have h := enstrophy_certificate ν f hν k hk forced hf x
  have squares : 0 ≤ ∑ i ∈ Finset.univ.erase forced, ((lam (k i) : ℝ) - 1) * x i ^ 2 := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr ?_) (sq_nonneg _)
    exact_mod_cast one_le_lam (hk i)
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

/-! ## The enstrophy ball, from `Nonlinear.lean` -/

/-- The enstrophy `Trapping`: weights `1`, centre `0`, `α = 2ν`, inner level
`f²/(4ν²)`, any trapped level `C > f²/(4ν²)`, and sup-norm radius `1 + C`, which
covers `{Z ≤ C}` since `C ≤ (1 + C)²`. -/
noncomputable def trappingZ (ν f : ℝ) (hν : 0 < ν) (C : ℝ) (hC : f ^ 2 / (4 * ν ^ 2) < C) :
    Nonlinear.Trapping n where
  weights := fun _ => 1
  centre := fun _ => 0
  alpha := 2 * ν
  inner := f ^ 2 / (4 * ν ^ 2)
  bound := C
  radius := 1 + C
  weights_pos := fun _ => one_pos
  alpha_pos := by linarith
  margin := hC
  radius_nonneg := by
    have hC0 : 0 ≤ C := le_trans (by positivity) hC.le
    linarith
  covers := fun _ => by
    have hC0 : 0 ≤ C := le_trans (by positivity) hC.le
    nlinarith [sq_nonneg C]

/-- The enstrophy `Trapping`'s `energy` is `enstrophy`. -/
theorem trappingZ_energy (ν f : ℝ) (hν : 0 < ν) (C : ℝ) (hC : f ^ 2 / (4 * ν ^ 2) < C)
    (x : Point n) : (trappingZ (n := n) ν f hν C hC).energy x = enstrophy x := by
  simp only [Nonlinear.Trapping.energy, trappingZ, enstrophy]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The enstrophy `Trapping`'s `rate` is `zrate`. -/
theorem trappingZ_rate (ν f : ℝ) (hν : 0 < ν) (C : ℝ) (hC : f ^ 2 / (4 * ν ^ 2) < C)
    (F : Point n → Point n) (x : Point n) :
    (trappingZ (n := n) ν f hν C hC).rate F x = zrate F x := by
  simp only [Nonlinear.Trapping.rate, trappingZ, zrate]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The enstrophy's differential inequality in the shape `Nonlinear.Trapping` consumes. -/
theorem decreaseZ (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (4 * ν ^ 2) < C)
    (x : Point n) :
    (trappingZ (n := n) ν f hν C hC).rate (field ν f k forced) x ≤
      (trappingZ (n := n) ν f hν C hC).alpha *
        ((trappingZ (n := n) ν f hν C hC).inner - (trappingZ (n := n) ν f hν C hC).energy x) := by
  rw [trappingZ_rate, trappingZ_energy]
  exact enstrophy_decrease_rate ν f hν k hk forced hf x

/-- **The enstrophy ball traps, for every member**: from any start with `Z ≤ C`,
`C > f²/(4ν²)`, a forward solution exists for all `t ≥ start`, it is unique, and
it keeps `Z ≤ C`. Uniform in the member: the level does not depend on the modes. -/
theorem trapped_enstrophy (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (C : ℝ) (hC : f ^ 2 / (4 * ν ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : enstrophy x₀ ≤ C) :
    (∃ state, Nonlinear.Solves (field ν f k forced) time x₀ state) ∧
    (∀ x y : Signal n, Nonlinear.Solves (field ν f k forced) time x₀ x →
      Nonlinear.Solves (field ν f k forced) time x₀ y → Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (field ν f k forced) time x₀ state →
      ∀ t ∈ time.domain, enstrophy (state t) ≤ C) := by
  have start : (trappingZ (n := n) ν f hν C hC).energy x₀ ≤ C := by rwa [trappingZ_energy]
  refine ⟨(trappingZ ν f hν C hC).exists_solution _ (contDiff_field ν f k forced)
      (decreaseZ ν f hν k hk forced hf C hC) time x₀ start,
    fun x y hx hy => (trappingZ ν f hν C hC).unique _ (contDiff_field ν f k forced)
      (decreaseZ ν f hν k hk forced hf C hC) time x₀ start hx hy,
    fun state h t ht => ?_⟩
  have bound := (trappingZ ν f hν C hC).invariant _ (decreaseZ ν f hν k hk forced hf C hC)
    time x₀ start state h t ht
  rwa [trappingZ_energy] at bound

/-- Every mode is bounded by `√C` on the enstrophy ball: `a_i² ≤ Z ≤ C`. -/
theorem mode_sq_le_enstrophy (x : Point n) (i : Fin n) : x i ^ 2 ≤ enstrophy x :=
  Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-! ## The unforced energy: small forcing, and the laminar line attracts

The unforced modes' energy `E_rest = Σ_{i ≠ forced} a_i²/λ(k i)` loses what the
triads through the forced mode feed it and nothing else: exactly,
`E_rest' = −2ν Z_rest − a_forced N_forced(a)`, where `N_forced` is the forced
mode's own cubic term. That term is bounded by the sum `K` of the forced mode's
coupling coefficients times `Z_rest`, so on the enstrophy ball `Z ≤ r²` the
unforced energy obeys `E_rest' ≤ −(2ν − K r) Z_rest ≤ −(2ν − K r) E_rest`, and
below the threshold `K r < 2ν` it decays exponentially: the laminar line
attracts, on the whole ball. -/

/-- The forced mode's cubic term, `N_forced(a) = Σ_{j,l} c(k j, k l, k forced) a_j a_l`. -/
noncomputable def forcedCubic (k : Fin n → Wave) (forced : Fin n) (x : Point n) : ℝ :=
  ∑ j, ∑ l, coefficient (k j) (k l) (k forced) * x j * x l

/-- The unforced modes' energy, `E − a_forced²/λ(k forced)`. -/
noncomputable def restEnergy (k : Fin n → Wave) (forced : Fin n) (x : Point n) : ℝ :=
  energy k x - x forced ^ 2 / lam (k forced)

/-- The unforced modes' enstrophy, `Z − a_forced²`. -/
noncomputable def restEnstrophy (forced : Fin n) (x : Point n) : ℝ :=
  enstrophy x - x forced ^ 2

/-- `E_rest'` along a field. -/
noncomputable def restRate (k : Fin n → Wave) (forced : Fin n) (F : Point n → Point n)
    (x : Point n) : ℝ :=
  rate k F x - 2 * x forced / lam (k forced) * F x forced

/-- The forced mode's coupling of an unordered pair, `(c(k j, k l, k forced) + c(k l, k j, k forced))/2`:
the cubic term is a quadratic form, and this is its symmetric matrix. -/
noncomputable def symCoefficient (k : Fin n → Wave) (forced : Fin n) (j l : Fin n) : ℝ :=
  (coefficient (k j) (k l) (k forced) + coefficient (k l) (k j) (k forced)) / 2

/-- The forced mode's coupling sum, `K = Σ_{j,l} |(c(k j, k l, k forced) + c(k l, k j, k forced))/2|`. -/
noncomputable def couplingSum (k : Fin n → Wave) (forced : Fin n) : ℝ :=
  ∑ j, ∑ l, |symCoefficient k forced j l|

/-- The cubic term through its symmetric matrix. -/
theorem forcedCubic_sym (k : Fin n → Wave) (forced : Fin n) (x : Point n) :
    forcedCubic k forced x = ∑ j, ∑ l, symCoefficient k forced j l * x j * x l := by
  have swap : ∑ j, ∑ l, coefficient (k l) (k j) (k forced) * x j * x l =
      ∑ j, ∑ l, coefficient (k j) (k l) (k forced) * x j * x l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have : ∑ j, ∑ l, symCoefficient k forced j l * x j * x l =
      (∑ j, ∑ l, coefficient (k j) (k l) (k forced) * x j * x l +
        ∑ j, ∑ l, coefficient (k l) (k j) (k forced) * x j * x l) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [symCoefficient]
    ring
  rw [this, swap, forcedCubic]
  ring

/-- A mode couples to nothing through itself: `(p × q) S(p, q, p) = 0`, since the
relations force `q = 0` or `q = ±2p`, where the cross product vanishes. -/
theorem cross_S_self_left (p q : Wave) (hp : p ≠ 0) (hq : q ≠ 0) :
    cross p q * S p q p = 0 := by
  rcases S_spec p q p hp hq with ⟨hA, hS⟩ | ⟨hB, hS⟩ | ⟨-, -, hS⟩
  · rcases hA with h | h
    · exact absurd (by rw [sub_eq_self] at h; exact h) hq
    · have hq2 : q = p + p := by linear_combination -h
      subst hq2
      simp only [cross, Prod.fst_add, Prod.snd_add]
      ring
  · rcases hB with h | h
    · exact absurd (by rw [add_eq_left] at h; exact h) hq
    · have hq2 : q = -(p + p) := by linear_combination h
      subst hq2
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      ring
  · rw [hS]
    ring

/-- Nor does anything couple to a mode through that mode: `(q × p) S(q, p, p) = 0`. -/
theorem cross_S_self_right (p q : Wave) (hp : p ≠ 0) (hq : q ≠ 0) :
    cross q p * S q p p = 0 := by
  rcases S_spec q p p hq hp with ⟨hA, hS⟩ | ⟨hB, hS⟩ | ⟨-, -, hS⟩
  · rcases hA with h | h
    · have hq2 : q = p + p := by linear_combination h
      subst hq2
      simp only [cross, Prod.fst_add, Prod.snd_add]
      ring
    · exact absurd (by rw [sub_eq_neg_self] at h; exact h) hq
  · rcases hB with h | h
    · exact absurd (by rw [add_eq_right] at h; exact h) hq
    · have hq2 : q = -(p + p) := by linear_combination h
      subst hq2
      simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
      ring
  · rw [hS]
    ring

theorem coefficient_self_left (p q : Wave) (hp : p ≠ 0) (hq : q ≠ 0) : coefficient p q p = 0 := by
  have h := cross_S_self_left p q hp hq
  have h' : (cross p q : ℝ) * S p q p = 0 := by exact_mod_cast h
  simp only [coefficient]
  rw [div_mul_eq_mul_div, div_eq_zero_iff]
  left
  exact h'

theorem coefficient_self_right (p q : Wave) (hp : p ≠ 0) (hq : q ≠ 0) :
    coefficient q p p = 0 := by
  have h := cross_S_self_right p q hp hq
  have h' : (cross q p : ℝ) * S q p p = 0 := by exact_mod_cast h
  simp only [coefficient]
  rw [div_mul_eq_mul_div, div_eq_zero_iff]
  left
  exact h'

/-- **The unforced energy identity**: `E_rest' = −2ν Z_rest − a_forced N_forced(a)`. -/
theorem rest_identity (ν f : ℝ) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (x : Point n) :
    restRate k forced (field ν f k forced) x =
      -2 * ν * restEnstrophy forced x - x forced * forcedCubic k forced x := by
  rw [restRate, energy_identity ν f k hk forced hf x, restEnstrophy]
  simp only [field, forcedCubic, hf, lam_one_one]
  push_cast
  ring

/-- `E_rest ≤ Z_rest`, since `λ ≥ 1`. -/
theorem restEnergy_le_restEnstrophy (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (x : Point n) : restEnergy k forced x ≤ restEnstrophy forced x := by
  rw [restEnergy, restEnstrophy, energy, enstrophy,
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2 / (lam (k i) : ℝ)) (Finset.mem_univ forced),
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ forced)]
  have each : ∀ i, x i ^ 2 / (lam (k i) : ℝ) ≤ x i ^ 2 := fun i =>
    div_le_self (sq_nonneg _) (by exact_mod_cast one_le_lam (hk i))
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ.erase forced) => each i
  linarith

/-- `0 ≤ E_rest`. -/
theorem restEnergy_nonneg (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (x : Point n) : 0 ≤ restEnergy k forced x := by
  rw [restEnergy, energy,
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2 / (lam (k i) : ℝ)) (Finset.mem_univ forced)]
  have : 0 ≤ ∑ i ∈ Finset.univ.erase forced, x i ^ 2 / (lam (k i) : ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (by exact_mod_cast (lam_pos (hk i)).le)
  linarith

/-- An unforced mode's square is at most `Z_rest`. -/
theorem sq_le_restEnstrophy (forced : Fin n) (x : Point n) {i : Fin n} (hi : i ≠ forced) :
    x i ^ 2 ≤ restEnstrophy forced x := by
  rw [restEnstrophy, enstrophy,
    ← Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ forced)]
  have := Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
    (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  linarith

/-- **The forced mode's cubic term is bounded by `K Z_rest`.** -/
theorem abs_forcedCubic_le (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (x : Point n) : |forcedCubic k forced x| ≤ couplingSum k forced * restEnstrophy forced x := by
  have term : ∀ j l, |symCoefficient k forced j l * x j * x l| ≤
      |symCoefficient k forced j l| * restEnstrophy forced x := by
    intro j l
    by_cases hj : j = forced
    · subst hj
      simp [symCoefficient, coefficient_self_left (k j) (k l) (hk j) (hk l),
        coefficient_self_right (k j) (k l) (hk j) (hk l)]
    by_cases hl : l = forced
    · subst hl
      simp [symCoefficient, coefficient_self_right (k l) (k j) (hk l) (hk j),
        coefficient_self_left (k l) (k j) (hk l) (hk j)]
    have hj2 := sq_le_restEnstrophy forced x hj
    have hl2 := sq_le_restEnstrophy forced x hl
    have prod : |x j * x l| ≤ restEnstrophy forced x := by
      rw [abs_mul]
      nlinarith [abs_nonneg (x j), abs_nonneg (x l), sq_abs (x j), sq_abs (x l),
        sq_nonneg (|x j| - |x l|)]
    rw [mul_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_left prod (abs_nonneg _)
  rw [forcedCubic_sym]
  calc |∑ j, ∑ l, symCoefficient k forced j l * x j * x l|
      ≤ ∑ j, ∑ l, |symCoefficient k forced j l * x j * x l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j, ∑ l, |symCoefficient k forced j l| * restEnstrophy forced x :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => term j l
    _ = couplingSum k forced * restEnstrophy forced x := by
        rw [couplingSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]

/-- On the enstrophy ball `Z ≤ r²`, `E_rest' ≤ −(2ν − K r) Z_rest`. -/
theorem rest_decrease_rate (ν f : ℝ) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (r : ℝ) (hr : 0 ≤ r) (x : Point n) (ball : enstrophy x ≤ r ^ 2) :
    restRate k forced (field ν f k forced) x ≤
      -(2 * ν - couplingSum k forced * r) * restEnstrophy forced x := by
  rw [rest_identity ν f k hk forced hf x]
  have forced_le : |x forced| ≤ r := by
    have sq : x forced ^ 2 ≤ r ^ 2 := (mode_sq_le_enstrophy x forced).trans ball
    exact abs_le.mpr (abs_le_of_sq_le_sq' sq hr)
  have cubic := abs_forcedCubic_le k hk forced x
  have K0 : 0 ≤ couplingSum k forced := Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => abs_nonneg _
  have Z0 : 0 ≤ restEnstrophy forced x := by
    rw [restEnstrophy]
    linarith [mode_sq_le_enstrophy x forced]
  have prod : x forced * forcedCubic k forced x ≥ -(r * (couplingSum k forced * restEnstrophy forced x)) := by
    have h := neg_abs_le (x forced * forcedCubic k forced x)
    rw [abs_mul] at h
    have := mul_le_mul forced_le cubic (abs_nonneg _) hr
    linarith
  nlinarith

/-- **Exponential decay of the unforced energy on the enstrophy ball**: along any
forward solution that keeps `Z ≤ r²`, with `γ = 2ν − K r ≥ 0`,
`E_rest(t) ≤ E_rest(start) e^{−γ (t − start)}` (at `γ = 0` this is monotone
decrease, not decay; `laminar_attracts` asks for `γ > 0`). -/
theorem rest_decay (ν f : ℝ) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (r : ℝ) (hr : 0 ≤ r) (hγ : 0 ≤ 2 * ν - couplingSum k forced * r)
    (time : TimeDomain) (x₀ : Point n) (state : Signal n)
    (h : Nonlinear.Solves (field ν f k forced) time x₀ state)
    (ball : ∀ t ∈ time.domain, enstrophy (state t) ≤ r ^ 2) :
    ∀ t ∈ time.domain, restEnergy k forced (state t) ≤
      restEnergy k forced x₀ *
        Real.exp (-(2 * ν - couplingSum k forced * r) * (t - time.start)) := by
  have derivative : ∀ t ∈ time.domain,
      HasDerivWithinAt (fun t => restEnergy k forced (state t))
        (restRate k forced (field ν f k forced) (state t)) time.domain t := by
    intro t ht
    have d := h.2 t ht
    have e : HasDerivWithinAt (fun t => energy k (state t)) (rate k (field ν f k forced) (state t))
        time.domain t := by
      have := HasDerivWithinAt.sum (u := Finset.univ)
        (A := fun i s => (state s i) ^ 2 / (lam (k i) : ℝ))
        (A' := fun i => (↑(2 : ℕ) * state t i ^ (2 - 1) * field ν f k forced (state t) i) /
          (lam (k i) : ℝ))
        (fun i _ => ((d i).pow 2).div_const (lam (k i) : ℝ))
      refine (this.congr (fun s _ => ?_) ?_).congr_deriv ?_
      · simp [energy, Finset.sum_apply]
      · simp [energy, Finset.sum_apply]
      · refine Finset.sum_congr rfl fun i _ => ?_
        norm_num
        ring
    have f' : HasDerivWithinAt (fun t => (state t forced) ^ 2 / (lam (k forced) : ℝ))
        ((↑(2 : ℕ) * state t forced ^ (2 - 1) * field ν f k forced (state t) forced) /
          (lam (k forced) : ℝ)) time.domain t :=
      ((d forced).pow 2).div_const _
    refine (e.sub f').congr_deriv ?_
    simp only [restRate]
    norm_num
    ring
  have decrease : ∀ t ∈ time.domain,
      restRate k forced (field ν f k forced) (state t) ≤
        -(2 * ν - couplingSum k forced * r) * restEnergy k forced (state t) := by
    intro t ht
    have step := rest_decrease_rate ν f k hk forced hf r hr (state t) (ball t ht)
    have le := restEnergy_le_restEnstrophy k hk forced (state t)
    nlinarith
  have := Dissipative.decay time (fun t => restEnergy k forced (state t))
    (fun t => restRate k forced (field ν f k forced) (state t))
    (2 * ν - couplingSum k forced * r) derivative decrease
  intro t ht
  have := this t ht
  rwa [h.1] at this

/-- **The laminar line attracts, for every member below the threshold**: from any
start with `Z ≤ r²`, where `r ≥ 0`, `f²/(4ν²) < r²` and `K r < 2ν`, a forward
solution exists for all `t ≥ start`, it is unique, it keeps `Z ≤ r²`, and its
unforced energy obeys `E_rest(t) ≤ E_rest(start) e^{−(2ν − K r)(t − start)}`. -/
theorem laminar_attracts (ν f : ℝ) (hν : 0 < ν) (k : Fin n → Wave) (hk : ∀ i, k i ≠ 0)
    (forced : Fin n) (hf : k forced = (1, 1)) (r : ℝ) (hr : 0 ≤ r)
    (hC : f ^ 2 / (4 * ν ^ 2) < r ^ 2) (hγ : 0 < 2 * ν - couplingSum k forced * r)
    (time : TimeDomain) (x₀ : Point n) (initial : enstrophy x₀ ≤ r ^ 2) :
    (∃ state, Nonlinear.Solves (field ν f k forced) time x₀ state) ∧
    (∀ x y : Signal n, Nonlinear.Solves (field ν f k forced) time x₀ x →
      Nonlinear.Solves (field ν f k forced) time x₀ y → Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (field ν f k forced) time x₀ state →
      ∀ t ∈ time.domain, enstrophy (state t) ≤ r ^ 2 ∧
        restEnergy k forced (state t) ≤
          restEnergy k forced x₀ *
            Real.exp (-(2 * ν - couplingSum k forced * r) * (t - time.start))) := by
  obtain ⟨ex, un, inv⟩ := trapped_enstrophy ν f hν k hk forced hf (r ^ 2) hC time x₀ initial
  refine ⟨ex, un, fun state h t ht => ⟨inv state h t ht, ?_⟩⟩
  exact rest_decay ν f k hk forced hf r hr hγ.le time x₀ state h (inv state h) t ht

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
#print axioms enstrophy_antisymm
#print axioms cubic_enstrophy_flux_zero
#print axioms enstrophy_identity
#print axioms enstrophy_certificate
#print axioms trapped_enstrophy
#print axioms rest_identity
#print axioms abs_forcedCubic_le
#print axioms rest_decay
#print axioms laminar_attracts

end Gimle.Forseti.GalerkinNS.Family
