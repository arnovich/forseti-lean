import Gimle.Forseti.ColeHopf

/-!
# Finite periodic heat profiles

A finite cosine profile has explicit spatial and time derivatives. Its absolute
coefficient moments bound the profile, its derivatives and the effect of removing
or perturbing modes. Positive profiles give actual classical Burgers fields via
the Cole–Hopf construction. The bounds below quantify squared normalized L2
error against an independent classical solution with the stated initial data.
-/
namespace Gimle.Forseti.ColeHopfFinite

open Set Real
open Gimle.Forseti.ColeHopf Gimle.Forseti.ClassicalVorticity
open Gimle.Forseti.ResidualPDE
open scoped BigOperators

variable {n : ℕ}

/-- Absolute coefficient moments; all frequencies are natural numbers. -/
noncomputable def moment (k : Fin n → ℕ) (a : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i, |a i| * (k i : ℝ) ^ j

/-- A weighted trigonometric heat sum. -/
noncomputable def wave (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∑ i, a i * (k i : ℝ) ^ j * exp (-ν * (k i : ℝ) ^ 2 * t) * f ((k i : ℝ) * x)

/-- A unit background plus finitely many decaying periodic heat modes. -/
noncomputable def profile (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ) : HeatJet where
  value := fun t x => 1 + wave ν k a 0 cos t x
  dx := fun t x => -wave ν k a 1 sin t x
  dxx := fun t x => -wave ν k a 2 cos t x
  dxxx := fun t x => wave ν k a 3 sin t x

/-- Moment budgets are nonnegative even when coefficients have mixed signs. -/
theorem moment_nonneg (k : Fin n → ℕ) (a : Fin n → ℝ) (j : ℕ) :
    0 ≤ moment k a j :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg (a i)) (pow_nonneg (Nat.cast_nonneg (k i)) j)

/-- A finite heat sum is jointly continuous for every continuous shape function. -/
theorem continuous_wave (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun z : ℝ × ℝ => wave ν k a j f z.1 z.2) := by
  unfold wave
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_fst))).mul
      (hf.comp (continuous_const.mul continuous_snd)))

/-- Differentiate a finite heat sum in space, increasing its frequency moment. -/
theorem deriv_wave_x (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (t x : ℝ) :
    HasDerivAt (wave ν k a j f t) (wave ν k a (j + 1) f' t x) x := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hf ((k i : ℝ) * x)).comp x ((hasDerivAt_id x).const_mul (k i : ℝ))).const_mul
      (a i * (k i : ℝ) ^ j * exp (-ν * (k i : ℝ) ^ 2 * t)))
  convert! h using 1
  unfold wave
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- Differentiate a finite heat sum in time, adding two frequency powers. -/
theorem deriv_wave_t (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) (f : ℝ → ℝ) (t x : ℝ) :
    HasDerivAt (fun s => wave ν k a j f s x)
      (-ν * wave ν k a (j + 2) f t x) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivAt_id t).const_mul (-ν * (k i : ℝ) ^ 2)).exp).const_mul
      (a i * (k i : ℝ) ^ j)).mul_const (f ((k i : ℝ) * x)))
  convert! h using 1
  unfold wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  simp only [id_eq]
  ring

/-- Shape negation is linear in a finite heat sum. -/
theorem wave_neg_shape (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) (f : ℝ → ℝ) (t x : ℝ) :
    wave ν k a j (fun y => -f y) t x = -wave ν k a j f t x := by
  simp [wave, Finset.sum_neg_distrib]

/-- Coefficient differences give the exact difference of finite heat sums. -/
theorem wave_sub (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (j : ℕ) (f : ℝ → ℝ) (t x : ℝ) :
    wave ν k a j f t x - wave ν k b j f t x =
      wave ν k (fun i => a i - b i) j f t x := by
  unfold wave
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Heat decay cannot enlarge a coefficient moment on nonnegative times. -/
theorem abs_wave_le (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) {f : ℝ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |wave ν k a j f t x| ≤ moment k a j := by
  unfold wave moment
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hpow : 0 ≤ (k i : ℝ) ^ j := pow_nonneg (Nat.cast_nonneg _) _
  have he : exp (-ν * (k i : ℝ) ^ 2 * t) ≤ 1 := by
    apply exp_le_one_iff.mpr
    have hn := mul_nonneg (mul_nonneg hν (sq_nonneg (k i : ℝ))) ht
    nlinarith only [hn]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpow,
    abs_of_pos (exp_pos _)]
  calc
    |a i| * (k i : ℝ) ^ j * exp (-ν * (k i : ℝ) ^ 2 * t) * |f ((k i : ℝ) * x)|
        ≤ |a i| * (k i : ℝ) ^ j * 1 * 1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg _) hpow))
        (hf _) (abs_nonneg _) (by positivity)
    _ = |a i| * (k i : ℝ) ^ j := by ring

/-- A positive denominator margin follows directly from the zeroth moment. -/
theorem value_lower (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    1 - moment k a 0 ≤ (profile ν k a).value t x := by
  have h := (abs_le.mp (abs_wave_le ν k a 0 abs_cos_le_one hν ht x)).1
  dsimp [profile]
  linarith only [h]

/-- The first absolute moment bounds the first spatial derivative. -/
theorem abs_dx_le (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |(profile ν k a).dx t x| ≤ moment k a 1 := by
  simpa only [profile, abs_neg] using abs_wave_le ν k a 1 abs_sin_le_one hν ht x

/-- The second absolute moment bounds the second spatial derivative. -/
theorem abs_dxx_le (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |(profile ν k a).dxx t x| ≤ moment k a 2 := by
  simpa only [profile, abs_neg] using abs_wave_le ν k a 2 abs_cos_le_one hν ht x

/-- The omitted zeroth moment bounds the heat-profile discrepancy. -/
theorem abs_value_sub_le (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |(profile ν k a).value t x - (profile ν k b).value t x| ≤
      moment k (fun i => a i - b i) 0 := by
  have he : (profile ν k a).value t x - (profile ν k b).value t x =
      wave ν k (fun i => a i - b i) 0 cos t x := by
    dsimp [profile]
    rw [show (1 + wave ν k a 0 cos t x) - (1 + wave ν k b 0 cos t x) =
      wave ν k a 0 cos t x - wave ν k b 0 cos t x by ring, wave_sub]
  rw [he]
  exact abs_wave_le ν k (fun i => a i - b i) 0 abs_cos_le_one hν ht x

/-- The omitted first moment bounds the derivative discrepancy. -/
theorem abs_dx_sub_le (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |(profile ν k a).dx t x - (profile ν k b).dx t x| ≤
      moment k (fun i => a i - b i) 1 := by
  have he : (profile ν k a).dx t x - (profile ν k b).dx t x =
      -wave ν k (fun i => a i - b i) 1 sin t x := by
    dsimp [profile]
    rw [show -wave ν k a 1 sin t x - -wave ν k b 1 sin t x =
      -(wave ν k a 1 sin t x - wave ν k b 1 sin t x) by ring, wave_sub]
  rw [he, abs_neg]
  exact abs_wave_le ν k (fun i => a i - b i) 1 abs_sin_le_one hν ht x

private theorem wave_periodic_cos (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) (t : ℝ) : Function.Periodic (wave ν k a j cos t) (2 * π) := by
  intro x
  unfold wave
  apply Finset.sum_congr rfl
  intro i _
  rw [show (k i : ℝ) * (x + 2 * π) = (k i : ℝ) * x + (k i : ℝ) * (2 * π) by ring,
    cos_add_nat_mul_two_pi]

private theorem wave_periodic_sin (ν : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (j : ℕ) (t : ℝ) : Function.Periodic (wave ν k a j sin t) (2 * π) := by
  intro x
  unfold wave
  apply Finset.sum_congr rfl
  intro i _
  rw [show (k i : ℝ) * (x + 2 * π) = (k i : ℝ) * x + (k i : ℝ) * (2 * π) by ring,
    sin_add_nat_mul_two_pi]

/-- The finite profile supplies all classical heat witnesses and positivity. -/
theorem valid (ν T : ℝ) (k : Fin n → ℕ) (a : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) : (profile ν k a).Valid ν T where
  deriv_x := by
    intro t _ x
    have h := (deriv_wave_x ν k a 0 (fun y => hasDerivAt_cos y) t x).const_add 1
    simpa only [profile, Nat.zero_add, wave_neg_shape] using h
  deriv_xx := by
    intro t _ x
    have h := (deriv_wave_x ν k a 1 (fun y => hasDerivAt_sin y) t x).neg
    simpa only [profile, Nat.reduceAdd, Pi.neg_def] using h
  deriv_xxx := by
    intro t _ x
    have h := (deriv_wave_x ν k a 2 (fun y => hasDerivAt_cos y) t x).neg
    simpa only [profile, Nat.reduceAdd, Pi.neg_def, wave_neg_shape, neg_neg] using h
  deriv_time := by
    intro t _ x
    have h := (deriv_wave_t ν k a 0 cos t x).const_add 1
    convert! h using 1
    simp only [profile, Nat.zero_add]
    ring
  deriv_time_dx := by
    intro t _ x
    have h := (deriv_wave_t ν k a 1 sin t x).neg
    convert! h using 1
    simp only [profile, Nat.reduceAdd]
    ring
  continuous_value :=
    (continuous_const.add (continuous_wave ν k a 0 continuous_cos)).continuousOn
  continuous_dx := (continuous_wave ν k a 1 continuous_sin).neg.continuousOn
  continuous_dxx := (continuous_wave ν k a 2 continuous_cos).neg.continuousOn
  continuous_dxxx := (continuous_wave ν k a 3 continuous_sin).continuousOn
  positive := fun t ht x => lt_of_lt_of_le (sub_pos.mpr ha) (value_lower ν k a hν ht.1 x)
  periodic_value := fun t _ x => congrArg (fun y => 1 + y) (wave_periodic_cos ν k a 0 t x)
  periodic_dx := fun t _ x => congrArg Neg.neg (wave_periodic_sin ν k a 1 t x)

/-- Initial pointwise error radius from coefficient differences and denominators. -/
noncomputable def initialRadius (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ) : ℝ :=
  2 * ν * (moment k (fun i => a i - b i) 1 / (1 - moment k a 0) +
    moment k b 1 * moment k (fun i => a i - b i) 0 /
      ((1 - moment k a 0) * (1 - moment k b 0)))

/-- Upper budget for the negative candidate slope, before the Young inequality. -/
noncomputable def growth (ν : ℝ) (k : Fin n → ℕ) (b : Fin n → ℝ) : ℝ :=
  2 * ν * moment k b 2 / (1 - moment k b 0)

/-- The pointwise error radius has the required nonnegative sign. -/
theorem initialRadius_nonneg (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) (hb : moment k b 0 < 1) :
    0 ≤ initialRadius ν k a b := by
  have hmA : 0 < 1 - moment k a 0 := sub_pos.mpr ha
  have hmB : 0 < 1 - moment k b 0 := sub_pos.mpr hb
  have hD0 := moment_nonneg k (fun i => a i - b i) 0
  have hD1 := moment_nonneg k (fun i => a i - b i) 1
  have hB1 := moment_nonneg k b 1
  unfold initialRadius
  positivity

/-- The finite moments bound the actual quotient discrepancy at every nonnegative time. -/
theorem pointwise_error_le (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) (hb : moment k b 0 < 1)
    {t : ℝ} (ht : 0 ≤ t) (p : ℝ × ℝ) :
    |((profile ν k a).burgersJet ν).value t p -
      ((profile ν k b).burgersJet ν).value t p| ≤ initialRadius ν k a b := by
  exact HeatJet.value_difference_le (profile ν k a) (profile ν k b)
    hν (sub_pos.mpr ha) (sub_pos.mpr hb)
    (value_lower ν k a hν ht p.1) (value_lower ν k b hν ht p.1)
    (abs_value_sub_le ν k a b hν ht p.1) (abs_dx_sub_le ν k a b hν ht p.1)
    (abs_dx_le ν k b hν ht p.1)

/-- The candidate's one-sided slope is bounded by its second moment. -/
theorem slope_le (ν : ℝ) (k : Fin n → ℕ) (b : Fin n → ℝ)
    (hν : 0 ≤ ν) (hb : moment k b 0 < 1) {t : ℝ} (ht : 0 ≤ t)
    (p : ℝ × ℝ) :
    -((profile ν k b).burgersJet ν).dx t p ≤ growth ν k b := by
  exact HeatJet.slope_le (profile ν k b) hν (sub_pos.mpr hb)
    (value_lower ν k b hν ht p.1) (abs_dxx_le ν k b hν ht p.1)

/-- The initial energy budget follows from the actual quotient's pointwise bound. -/
theorem initial_energy_le (ν : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) (hb : moment k b 0 < 1) :
    energy ((profile ν k a).burgersJet ν) ((profile ν k b).burgersJet ν) 0 ≤
      initialRadius ν k a b ^ 2 := by
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hA := (valid ν 0 k a hν ha).regular
  have hB := (valid ν 0 k b hν hb).regular
  have hc := (continuous_slice hA.continuous_value (by simp : (0 : ℝ) ∈ Icc 0 0)).sub
    (continuous_slice hB.continuous_value (by simp : (0 : ℝ) ∈ Icc 0 0))
  have h := squareAverage_mono hL
    (f := fun p => (((profile ν k a).burgersJet ν).value 0 p -
      ((profile ν k b).burgersJet ν).value 0 p) ^ 2)
    (g := fun _ => initialRadius ν k a b ^ 2) (hc.pow 2) continuous_const
    (fun x _ y _ => sq_le_sq.mpr (by
      rw [abs_of_nonneg (initialRadius_nonneg ν k a b hν ha hb)]
      exact pointwise_error_le ν k a b hν ha hb (le_refl 0) (x,y)))
  simpa only [energy, squareAverage_const hL] using h

/-- One reusable error argument covers every independent admitted classical solution.
The initial field is specified explicitly; the finite full profile also witnesses existence. -/
theorem comparison_against (ν T : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) (hb : moment k b 0 < 1) (hT : 0 ≤ T)
    {u : SpatialJet} {ut : Field}
    (hu : Burgers ν T (fun _ _ => 0) (fun _ _ => 0) u ut)
    (hinit : ∀ p, u.value 0 p = ((profile ν k a).burgersJet ν).value 0 p) :
    ∀ t ∈ Icc 0 T, energy u ((profile ν k b).burgersJet ν) t ≤
      gronwallBound (initialRadius ν k a b ^ 2) (growth ν k b + 1) 0 t := by
  have hi : energy u ((profile ν k b).burgersJet ν) 0 ≤ initialRadius ν k a b ^ 2 := by
    have he : energy u ((profile ν k b).burgersJet ν) 0 =
        energy ((profile ν k a).burgersJet ν) ((profile ν k b).burgersJet ν) 0 := by
      unfold energy
      congr 1
      funext p
      rw [hinit p]
    rw [he]
    exact initial_energy_le ν k a b hν ha hb
  have h := hu.error_le_envelope (valid ν T k b hν hb).burgers
    (M := growth ν k b) (R := 0) hν hT hi
    (fun _ _ => continuous_const)
    (fun t ht x _ y _ => slope_le ν k b hν hb ht.1.le (x,y))
    (by intros; simp [squareAverage_const (show 0 < 2 * π from mul_pos (by norm_num) pi_pos)])
  simpa only [zero_pow (by decide : 2 ≠ 0)] using h

/-- The finite full profile is itself an exact solution admitted by the universal comparison. -/
theorem comparison (ν T : ℝ) (k : Fin n → ℕ) (a b : Fin n → ℝ)
    (hν : 0 ≤ ν) (ha : moment k a 0 < 1) (hb : moment k b 0 < 1) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      energy ((profile ν k a).burgersJet ν) ((profile ν k b).burgersJet ν) t ≤
        gronwallBound (initialRadius ν k a b ^ 2) (growth ν k b + 1) 0 t :=
  comparison_against ν T k a b hν ha hb hT (valid ν T k a hν ha).burgers (fun _ => rfl)

#print axioms valid
#print axioms abs_value_sub_le
#print axioms abs_dx_sub_le
#print axioms comparison_against
#print axioms comparison

end Gimle.Forseti.ColeHopfFinite
