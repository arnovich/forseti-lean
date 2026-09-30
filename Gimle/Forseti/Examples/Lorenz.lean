import Gimle.Forseti.LinearEnergyContract
import Gimle.Forseti.Dissipative
import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Compile.Syntax

/-! # The Lorenz system stays in a ball: a nonlinear trajectory contract

`x' = σ(y − x)`, `y' = x(ρ − z) − y`, `z' = xy − βz` with `σ = 10`, `ρ = 28`,
`β = 8/3`, from `(1, 1, 1)` at `t = 0`, observing `V = x² + y² + (z − σ − ρ)²`,
`σ + ρ = 38`.

Along every solution `V' = −2σx² − 2y² − 2βz² + 2β(σ+ρ)z`, so
`V' + 2V ≤ 2·1541` at every state (the least constant is `23104/15`), and
`Dissipative.sublevel` gives `V ≤ 1600` forever from `V(0) = 1371`. This is the
first trajectory contract here whose field has no linear view: existence and
forward uniqueness are proved by hand. -/

namespace Gimle.Forseti.Examples.Lorenz

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard Gimle.Asgard.Model Polynomial

/-- The Lorenz equations with the classical parameters and the observed
storage `V = x² + y² + (z − 38)²`, `38 = σ + ρ`. -/
def body : Body := {
  program := ⟨[⟨"state-x", "x", .state⟩, ⟨"state-y", "y", .state⟩,
      ⟨"state-z", "z", .state⟩, ⟨"param-s", "s", .parameter⟩,
      ⟨"param-r", "r", .parameter⟩, ⟨"param-b", "b", .parameter⟩],
    equations% {
      dx := s * (y - x);
      dy := x * (r - z) - y;
      dz := x * y - b * z;
      V := sqx + sqy + sqw;
      sqx := x ^ 2;
      sqy := y ^ 2;
      sqw := w ^ 2;
      w := z - 38;
    }⟩
  parameters := [⟨"param-s", 10⟩, ⟨"param-r", 28⟩, ⟨"param-b", 8 / 3⟩]
  observations := [⟨⟨"obs-x", "x", .output⟩, "state-x"⟩,
    ⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-z", "z", .output⟩, "state-z"⟩,
    ⟨⟨"obs-v", "V", .output⟩, "V"⟩]
}

/-- State order `[x, y, z]`, from `(1, 1, 1)` at `t = 0`. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩,
    ⟨"state-z", "dz", "initial-z"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-y", "y0", .initial⟩,
    ⟨"initial-z", "z0", .initial⟩]
  initialValues := [⟨"initial-x", 1⟩, ⟨"initial-y", 1⟩, ⟨"initial-z", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def compiled : ContinuousModel body evolution :=
  (compileContinuous body evolution).toOption.get (by decide +kernel)

/-- The compiled right-hand sides, in state order `[x, y, z]`, as the compiler
normalises them. Private: `rates_formula` is the statement to depend on. -/
private theorem rates_expressions : compiled.rates.expressions =
    (![.mul (.constant 10) (.add (.var 1) (.neg (.var 0))),
      .add (.mul (.var 0) (.add (.constant 28) (.neg (.var 2)))) (.neg (.var 1)),
      .add (.mul (.var 0) (.var 1)) (.neg (.mul (.constant (8 / 3)) (.var 2)))] :
      Fin 3 → Expr 3) := by decide +kernel

theorem initial_eq : compiled.initial = (![1, 1, 1] : Point 3) := by
  change (fun i : Fin 3 => (compiled.initials i : ℝ)) = _
  have values : compiled.initials = ![1, 1, 1] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- The Lorenz field in closed form. -/
noncomputable def field (x : Point 3) : Point 3 :=
  ![10 * (x 1 - x 0), x 0 * (28 - x 2) - x 1, x 0 * x 1 - 8 / 3 * x 2]

theorem rates_formula (x : Point 3) : compiled.rates.circuit.run x = field x := by
  rw [Selected.circuit, compileOutputs_correct, rates_expressions]
  ext i
  change Fin 3 at i
  fin_cases i <;> norm_num [field, Expr.eval, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

theorem rates_eval (i : Fin evolution.states.length) (x : Point evolution.states.length) :
    (compiled.rates.expressions i).eval x = field x i := by
  have h := congrFun (rates_formula x) i
  rwa [Selected.circuit, compileOutputs_correct] at h

/-- `V` is the fourth observation. -/
def energyIndex : Fin body.observations.length := ⟨3, by decide⟩

/-- The storage `V = x² + y² + (z − 38)²`. -/
noncomputable def energy (x : Point 3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + (x 2 - 38) ^ 2

/-- The observation's normal form. Private: `energy_at` is the statement to depend on. -/
private theorem energy_expression : compiled.outputs.expressions energyIndex =
    (.add (.add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)))
      (.mul (.mul (.constant 1) (.add (.var 2) (.neg (.constant 38))))
        (.add (.var 2) (.neg (.constant 38)))) : Expr 3) := by
  decide +kernel

theorem energy_at (x : Point 3) :
    compiled.outputs.circuit.run x energyIndex = energy x := by
  rw [Selected.circuit, compileOutputs_correct]
  change (compiled.outputs.expressions energyIndex).eval x = _
  rw [energy_expression]
  simp [energy, Expr.eval, pow_two, sub_eq_add_neg]

theorem energy_at_initial :
    compiled.outputs.circuit.run compiled.initial energyIndex = 1371 := by
  rw [energy_at, initial_eq]
  norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## Realizations, as solutions of the closed-form field -/

theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by
  simp [Dynamics.TimeDomain.domain, Evolution.time, evolution]

theorem domain_eq : evolution.time.domain = Set.Ici 0 := by
  ext t
  rw [Set.mem_Ici]
  exact domain_iff t

/-- A realization is a forward solution of `field` from `(1, 1, 1)`. -/
theorem realizes_iff (state : Dynamics.Signal 3) :
    compiled.Realizes state ↔
      state 0 = (![1, 1, 1] : Point 3) ∧
      ∀ t ∈ evolution.time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        (field (state t) i) evolution.time.domain t := by
  rw [← compiled.solves_iff_realizes, compiled.solves_iff_field, initial_eq]
  have start : evolution.time.start = 0 := by simp [Evolution.time, evolution]
  rw [start]
  apply and_congr_right
  intro _
  constructor
  · intro h t ht i
    have := h t ht i
    rwa [rates_eval] at this
  · intro h t ht i
    have := h t ht i
    rwa [← rates_eval] at this

/-- The rate of `V`: the cubic terms cancel and only the damping and the
`z`-shift remain. -/
noncomputable def rate (x : Point 3) : ℝ :=
  -20 * x 0 ^ 2 - 2 * x 1 ^ 2 - 16 / 3 * x 2 ^ 2 + 608 / 3 * x 2

theorem energy_derivative (state : Dynamics.Signal 3) (realized : compiled.Realizes state)
    (t : ℝ) (within : t ∈ evolution.time.domain) :
    HasDerivWithinAt (fun t => energy (state t)) (rate (state t)) evolution.time.domain t := by
  have dx := ((realizes_iff state).mp realized).2 t within 0
  have dy := ((realizes_iff state).mp realized).2 t within 1
  have dz := ((realizes_iff state).mp realized).2 t within 2
  have h := ((dx.pow 2).add (dy.pow 2)).add ((dz.sub_const 38).pow 2)
  convert! h using 1
  simp only [field, rate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The algebraic heart: `V' + 2V ≤ 2·1541` at every state. The least constant
for which this holds is `23104/15 ≈ 1540.27`; the margin to `1600` is what makes
the fencing argument below strict. -/
theorem storage_bound (x : Point 3) : rate x ≤ 2 * 1541 - 2 * energy x := by
  unfold rate energy
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2 - 38 / 5)]

/-- Every realization keeps `V ≤ 1600`: `Dissipative.sublevel` on the
differential inequality `V' ≤ 2(1600 − V)`, from `V(0) = 1371`. -/
theorem invariant (state : Dynamics.Signal 3) (realized : compiled.Realizes state) :
    Always evolution.time (fun x => energy x ≤ 1600) state := by
  have initial : energy (state evolution.time.start) = 1371 := by
    have start : evolution.time.start = 0 := by simp [Evolution.time, evolution]
    rw [start, ((realizes_iff state).mp realized).1]
    norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons]
  exact Dissipative.sublevel evolution.time (fun t => energy (state t))
    (fun t => rate (state t)) 2 1600 (energy_derivative state realized)
    (fun t _ => by linarith [storage_bound (state t)]) (by rw [initial]; norm_num)

/-! ## Existence for all `t ≥ 0`, by hand

Mathlib's Picard–Lindelöf theorem is local. The field is clamped to a box
containing `{V ≤ 1600}`, which makes it bounded and globally Lipschitz, so a
solution exists on every `[0, n]`; those are glued by uniqueness into one
solution on `[0, ∞)`. A fencing argument keeps it inside the sublevel set,
where the clamped and the true field agree, so it solves the Lorenz system. -/

/-- The box's centre, `(0, 0, 38)`. -/
noncomputable def centre : Point 3 := ![0, 0, 38]

/-- The closed sup-norm box of radius `40` about the centre. -/
noncomputable def box : Set (Point 3) := Metric.closedBall centre 40

theorem mem_box_of_energy {x : Point 3} (h : energy x ≤ 1600) : x ∈ box := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
  intro i
  rw [Real.dist_eq, abs_le]
  unfold energy at h
  have sq : (x i - centre i) ^ 2 ≤ 40 ^ 2 := by
    fin_cases i <;> simp [centre] <;>
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2 - 38)]
  exact abs_le_of_sq_le_sq' sq (by norm_num)

theorem field_contDiff : ContDiff ℝ 1 field := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

theorem field_lipschitz : ∃ K : NNReal, LipschitzOnWith K field box :=
  field_contDiff.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)

/-- Each coordinate projected onto the box's interval; the identity on the box. -/
noncomputable def clamp (x : Point 3) : Point 3 :=
  fun i => (Set.projIcc (centre i - 40) (centre i + 40) (by linarith) (x i) : ℝ)

theorem clamp_mem_box (x : Point 3) : clamp x ∈ box := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
  intro i
  rw [Real.dist_eq, abs_le]
  obtain ⟨lo, hi⟩ :=
    Set.mem_Icc.mp (Set.projIcc (centre i - 40) (centre i + 40) (by linarith) (x i)).2
  simp only [clamp]
  constructor <;> linarith

theorem clamp_of_mem_box {x : Point 3} (h : x ∈ box) : clamp x = x := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff (by norm_num)] at h
  funext i
  have hi := abs_le.mp ((Real.dist_eq _ _) ▸ h i)
  have inside : x i ∈ Set.Icc (centre i - 40) (centre i + 40) := ⟨by linarith, by linarith⟩
  simp [clamp, Set.projIcc_of_mem _ inside]

theorem clamp_lipschitz : LipschitzWith 1 clamp := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  calc dist (clamp x i) (clamp y i) ≤ dist (x i) (y i) := by
        have := (LipschitzWith.projIcc (a := centre i - 40) (b := centre i + 40)
          (by linarith)).dist_le_mul (x i) (y i)
        simpa [clamp, Subtype.dist_eq] using this
    _ ≤ dist x y := dist_le_pi_dist x y i

/-- The Lorenz field read through the clamp: the true field on the box. -/
noncomputable def clamped (x : Point 3) : Point 3 := field (clamp x)

theorem clamped_of_mem_box {x : Point 3} (h : x ∈ box) : clamped x = field x := by
  simp [clamped, clamp_of_mem_box h]

theorem clamped_lipschitz : ∃ K : NNReal, LipschitzWith K clamped := by
  obtain ⟨K, hK⟩ := field_lipschitz
  refine ⟨K * 1, ?_⟩
  rw [← lipschitzOnWith_univ]
  exact hK.comp clamp_lipschitz.lipschitzOnWith (fun x _ => clamp_mem_box x)

theorem clamped_bound : ∃ L : ℝ, ∀ x, ‖clamped x‖ ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_closedBall centre 40).exists_bound_of_continuousOn
    field_contDiff.continuous.continuousOn
  exact ⟨L, fun x => hL _ (clamp_mem_box x)⟩

/-- Picard–Lindelöf for the clamped field on `[0, n]`, from `(1, 1, 1)`. -/
theorem clamped_solution_on (n : ℕ) : ∃ α : ℝ → Point 3, α 0 = ![1, 1, 1] ∧
    ∀ t ∈ Set.Icc (0 : ℝ) n, HasDerivWithinAt α (clamped (α t)) (Set.Icc (0 : ℝ) n) t := by
  obtain ⟨K, hK⟩ := clamped_lipschitz
  obtain ⟨L, hL⟩ := clamped_bound
  let L' : NNReal := ⟨max L 0, le_max_right _ _⟩
  let a : NNReal := L' * n
  have pl : IsPicardLindelof (fun _ => clamped) (tmin := 0) (tmax := n) ⟨0, by simp⟩
      (![1, 1, 1] : Point 3) a 0 L' K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => (hL x).trans (le_max_left _ _))
      hK.lipschitzOnWith ?_
    simp only [a, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_zero, sub_zero]
    rw [max_eq_left (by linarith [Nat.cast_nonneg (α := ℝ) n])]
  obtain ⟨α, h0, hd⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hd⟩

private theorem Icc_mem_nhdsWithin_Ici_of_lt {a c t b : ℝ} (ha : a ≤ c) (hb : t < b) :
    Set.Icc a b ∈ nhdsWithin t (Set.Ici c) := by
  apply Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici c) (Iio_mem_nhds hb))
  intro s hs
  exact ⟨ha.trans hs.1, hs.2.le⟩

/-- Two solutions of the clamped field from the same point agree on `[0, b]`. -/
theorem clamped_unique_on (b : ℝ) (α β : ℝ → Point 3)
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivWithinAt α (clamped (α t)) (Set.Icc (0 : ℝ) b) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivWithinAt β (clamped (β t)) (Set.Icc (0 : ℝ) b) t)
    (h0 : α 0 = β 0) : Set.EqOn α β (Set.Icc 0 b) := by
  obtain ⟨K, hK⟩ := clamped_lipschitz
  refine ODE_solution_unique (v := fun _ => clamped) (fun _ => hK) ?_ ?_ ?_ ?_ h0
  · exact fun t ht => (hα t ht).continuousWithinAt
  · intro t ht
    exact (hα t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_of_lt ht.1 ht.2)
  · exact fun t ht => (hβ t ht).continuousWithinAt
  · intro t ht
    exact (hβ t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_of_lt ht.1 ht.2)

/-- The chosen solution on `[0, n]`. -/
noncomputable def piece (n : ℕ) : ℝ → Point 3 := Classical.choose (clamped_solution_on n)

theorem piece_zero (n : ℕ) : piece n 0 = ![1, 1, 1] :=
  (Classical.choose_spec (clamped_solution_on n)).1

theorem piece_deriv (n : ℕ) : ∀ t ∈ Set.Icc (0 : ℝ) n,
    HasDerivWithinAt (piece n) (clamped (piece n t)) (Set.Icc (0 : ℝ) n) t :=
  (Classical.choose_spec (clamped_solution_on n)).2

theorem piece_agree {m n : ℕ} (h : m ≤ n) : Set.EqOn (piece m) (piece n) (Set.Icc 0 m) := by
  have cast : (m : ℝ) ≤ n := by exact_mod_cast h
  refine clamped_unique_on m (piece m) (piece n) (piece_deriv m) ?_ (by rw [piece_zero, piece_zero])
  intro t ht
  exact (piece_deriv n t ⟨ht.1, ht.2.trans cast⟩).mono (Set.Icc_subset_Icc le_rfl cast)

/-- The pieces glued: at `t`, the piece on `[0, ⌈t⌉ + 1]`. -/
noncomputable def glued (t : ℝ) : Point 3 := piece (⌈t⌉₊ + 1) t

private theorem lt_ceil_succ (t : ℝ) : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
  push_cast
  linarith [Nat.le_ceil t]

theorem glued_eq_piece {n : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) n) : glued t = piece n t := by
  unfold glued
  rcases le_total (⌈t⌉₊ + 1) n with h | h
  · exact piece_agree h ⟨ht.1, (lt_ceil_succ t).le⟩
  · exact (piece_agree h ht).symm

theorem glued_zero : glued 0 = ![1, 1, 1] := by
  rw [glued_eq_piece (n := 1) ⟨le_rfl, by norm_num⟩, piece_zero]

theorem glued_deriv (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt glued (clamped (glued t)) (Set.Ici 0) t := by
  have tn := lt_ceil_succ t
  have mem : Set.Icc (0 : ℝ) (⌈t⌉₊ + 1 : ℕ) ∈ nhdsWithin t (Set.Ici 0) :=
    Icc_mem_nhdsWithin_Ici_of_lt le_rfl tn
  have h := (piece_deriv (⌈t⌉₊ + 1) t ⟨ht, tn.le⟩).mono_of_mem_nhdsWithin mem
  rw [← glued_eq_piece ⟨ht, tn.le⟩] at h
  exact h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem mem fun s hs => glued_eq_piece hs)
    (glued_eq_piece ⟨ht, tn.le⟩)

/-- The rate of `V` along the clamped field. -/
noncomputable def clampedRate (x : Point 3) : ℝ :=
  2 * x 0 * clamped x 0 + 2 * x 1 * clamped x 1 + 2 * (x 2 - 38) * clamped x 2

theorem clampedRate_of_mem_box {x : Point 3} (h : x ∈ box) : clampedRate x = rate x := by
  simp only [clampedRate, clamped_of_mem_box h, field, rate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem glued_energy_deriv (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => energy (glued t)) (clampedRate (glued t)) (Set.Ici 0) t := by
  have d := hasDerivWithinAt_pi.mp (glued_deriv t ht)
  have h := (((d 0).pow 2).add ((d 1).pow 2)).add (((d 2).sub_const 38).pow 2)
  convert! h using 1
  simp only [clampedRate]
  ring

/-- Fencing: the glued solution never leaves `{V ≤ 1600}`. At a contact point the
clamp is the identity, and there `V' = rate ≤ 2·1541 − 2·1600 = −118 < 0`. -/
theorem glued_energy_le (t : ℝ) (ht : 0 ≤ t) : energy (glued t) ≤ 1600 := by
  have fence := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => energy (glued s))
    (f' := fun s => clampedRate (glued s)) (a := 0) (b := t)
    (fun s hs => ((glued_energy_deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (glued_energy_deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => 1600) (B' := fun _ => 0)
    (by simp only [glued_zero]; norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons])
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : energy (glued s) = 1600)
      have inbox : glued s ∈ box := mem_box_of_energy contact.le
      show clampedRate (glued s) < 0
      rw [clampedRate_of_mem_box inbox]
      have := storage_bound (glued s)
      rw [contact] at this
      linarith)
  exact fence ⟨ht, le_rfl⟩

/-- The glued solution solves the Lorenz system: on the sublevel set the clamped
and the true field agree. -/
theorem glued_realizes : compiled.Realizes glued := by
  rw [realizes_iff]
  refine ⟨glued_zero, ?_⟩
  intro t ht i
  have ht0 := (domain_iff t).mp ht
  have d := glued_deriv t ht0
  rw [clamped_of_mem_box (mem_box_of_energy (glued_energy_le t ht0))] at d
  rw [domain_eq]
  exact hasDerivWithinAt_pi.mp d i

theorem compiled_exists : ∃ state, compiled.Realizes state := ⟨glued, glued_realizes⟩

/-! ## Forward uniqueness, on the compact sublevel set -/

theorem compiled_unique {x y : Dynamics.Signal 3}
    (hx : compiled.Realizes x) (hy : compiled.Realizes y) :
    Set.EqOn x y evolution.time.domain := by
  obtain ⟨K, hK⟩ := field_lipschitz
  have hx' := (realizes_iff x).mp hx
  have hy' := (realizes_iff y).mp hy
  have vec (z : Dynamics.Signal 3)
      (hz : ∀ t ∈ evolution.time.domain, ∀ i, HasDerivWithinAt (fun t => z t i)
        (field (z t) i) evolution.time.domain t) (s : ℝ) (hs : 0 ≤ s) :
      HasDerivWithinAt z (field (z s)) evolution.time.domain s :=
    hasDerivWithinAt_pi.mpr fun i => hz s ((domain_iff s).mpr hs) i
  intro t ht
  have ht0 := (domain_iff t).mp ht
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => field) (s := fun _ => box)
    (a := 0) (b := t) (fun _ _ => hK) ?_ ?_ ?_ ?_ ?_ ?_ (hx'.1.trans hy'.1.symm) ⟨ht0, le_rfl⟩
  · exact fun s hs => (vec x hx'.2 s hs.1).continuousWithinAt.mono
      fun r hr => (domain_iff r).mpr hr.1
  · exact fun s hs => (vec x hx'.2 s hs.1).mono fun r hr => (domain_iff r).mpr (hs.1.trans hr)
  · exact fun s hs => mem_box_of_energy (invariant x hx s ((domain_iff s).mpr hs.1))
  · exact fun s hs => (vec y hy'.2 s hs.1).continuousWithinAt.mono
      fun r hr => (domain_iff r).mpr hr.1
  · exact fun s hs => (vec y hy'.2 s hs.1).mono fun r hr => (domain_iff r).mpr (hs.1.trans hr)
  · exact fun s hs => mem_box_of_energy (invariant y hy s ((domain_iff s).mpr hs.1))

/-! ## The contract, in the interface gimle-forseti's trajectory registry cites -/

def observed := LinearEnergyContract.observed compiled

def admitted : Trajectory.SignalPredicate (0 + evolution.states.length) :=
  LinearEnergyContract.admitted compiled

theorem feedback_reads (input : Dynamics.Signal (0 + evolution.states.length))
    (admit : admitted input) (state : Dynamics.Signal evolution.states.length) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=
  LinearEnergyContract.feedback_reads compiled input admit state

theorem declared_input_admitted :
    admitted (Dynamics.signalAppend Model.noDrivers fun _ => compiled.initial) :=
  LinearEnergyContract.declared_input_admitted compiled

/-- The loop's contract: a trajectory exists, is unique forward, and keeps the
observed `V` in `[0, 1600]`. -/
theorem loop_contract :
    Contract compiled.feedback evolution.time admitted
      (Always evolution.time fun x =>
        0 ≤ compiled.outputs.circuit.run x energyIndex ∧
        compiled.outputs.circuit.run x energyIndex ≤ 1600) where
  realizable input admit := ⟨glued, (feedback_reads input admit glued).mpr glued_realizes⟩
  unique input admit x y hx hy :=
    compiled_unique ((feedback_reads input admit x).mp hx) ((feedback_reads input admit y).mp hy)
  holds input admit state realized t ht := by
    dsimp only
    rw [energy_at]
    exact ⟨by unfold energy; positivity,
      invariant state ((feedback_reads input admit state).mp realized) t ht⟩

/-- **The Lorenz trajectory stays in the ball `V ≤ 1600`**, for every admitted input. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 1600) :=
  Contract.compose loop_contract
    (Contract.lift compiled.outputs.circuit evolution.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- `1300` is not a bound: `V = 1371` at the start. -/
theorem thirteen_hundred_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 1300) := by
  intro claim
  have start : glued evolution.time.start = compiled.initial := by
    rw [initial_eq]
    have : evolution.time.start = 0 := by simp [Evolution.time, evolution]
    rw [this, glued_zero]
  have bounded := claim _ declared_input_admitted _
    ⟨glued, (feedback_reads _ declared_input_admitted glued).mpr glued_realizes, rfl⟩
    evolution.time.start (by simp [Dynamics.TimeDomain.domain])
  simp only at bounded
  rw [start, energy_at_initial] at bounded
  norm_num at bounded

#print axioms invariant
#print axioms compiled_exists
#print axioms compiled_unique
#print axioms energy_contract
#print axioms thirteen_hundred_refuted

end Gimle.Forseti.Examples.Lorenz
