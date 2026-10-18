import Gimle.Forseti.BernsteinMatrix

/-! A small executable rational polynomial checker. The list representation needs
no canonical-form invariant: acceptance is sufficient for equality of evaluations.
All arithmetic and the acceptance test can be reduced by the ordinary kernel. -/
namespace Gimle.Forseti.RationalPolynomial

structure Term where
  timeDegree : Nat
  parameterDegree : Nat
  coefficient : ℚ
  deriving DecidableEq

abbrev Poly := List Term

noncomputable def termEval (t : Term) (s u : ℝ) : ℝ :=
  t.coefficient * s ^ t.timeDegree * u ^ t.parameterDegree

noncomputable def eval (p : Poly) (s u : ℝ) : ℝ :=
  (p.map (fun t => termEval t s u)).sum

/-- Collect a term at the first matching degree; no sorting assumption is needed. -/
def insert (t : Term) : Poly → Poly
  | [] => [t]
  | h :: rest =>
    if t.timeDegree = h.timeDegree ∧ t.parameterDegree = h.parameterDegree then
      { h with coefficient := t.coefficient + h.coefficient } :: rest
    else h :: insert t rest

def add (p q : Poly) : Poly := p.foldr insert q

def neg (p : Poly) : Poly := p.map fun t => { t with coefficient := -t.coefficient }

def multiplyTerm (t h : Term) : Term :=
  ⟨t.timeDegree + h.timeDegree, t.parameterDegree + h.parameterDegree,
    t.coefficient * h.coefficient⟩

def mul (p q : Poly) : Poly :=
  p.foldr (fun t rest => add (q.map (multiplyTerm t)) rest) []

def constant (a : ℚ) : Poly := [⟨0, 0, a⟩]
def time : Poly := [⟨1, 0, 1⟩]
def parameter : Poly := [⟨0, 1, 1⟩]

def power (p : Poly) : Nat → Poly
  | 0 => constant 1
  | n + 1 => mul p (power p n)

def sum (ps : List Poly) : Poly := ps.foldr add []

def finSum {n : Nat} (p : Fin n → Poly) : Poly := sum (List.ofFn p)

/-- Sufficient, deliberately one-way test; arbitrary lists may contain duplicates. -/
def equivalent (p q : Poly) : Bool :=
  (add p (neg q)).all fun t => t.coefficient == 0

@[simp] theorem eval_nil (s u : ℝ) : eval [] s u = 0 := rfl

@[simp] theorem eval_cons (t : Term) (p : Poly) (s u : ℝ) :
    eval (t :: p) s u = termEval t s u + eval p s u := rfl

theorem eval_insert (t : Term) (p : Poly) (s u : ℝ) :
    eval (insert t p) s u = termEval t s u + eval p s u := by
  induction p with
  | nil => simp [insert]
  | cons h rest ih =>
    simp only [insert]
    split
    · rename_i he
      simp only [eval_cons, termEval, Rat.cast_add, he.1, he.2]
      ring
    · simp only [eval_cons, ih]
      ring

@[simp] theorem eval_add (p q : Poly) (s u : ℝ) :
    eval (add p q) s u = eval p s u + eval q s u := by
  induction p with
  | nil => simp [add]
  | cons t rest ih =>
    simpa only [add, List.foldr_cons, eval_insert, eval_cons, add_assoc] using
      congrArg (fun x => termEval t s u + x) ih

@[simp] theorem eval_neg (p : Poly) (s u : ℝ) : eval (neg p) s u = -eval p s u := by
  induction p with
  | nil => simp [neg]
  | cons t rest ih =>
    simp only [neg, List.map_cons, eval_cons] at *
    rw [ih]
    simp [termEval]
    ring

theorem eval_multiplyTerm (t : Term) (q : Poly) (s u : ℝ) :
    eval (q.map (multiplyTerm t)) s u = termEval t s u * eval q s u := by
  induction q with
  | nil => simp
  | cons h rest ih =>
    simp only [List.map_cons, eval_cons, ih, termEval, multiplyTerm, Rat.cast_mul,
      pow_add]
    ring

@[simp] theorem eval_mul (p q : Poly) (s u : ℝ) :
    eval (mul p q) s u = eval p s u * eval q s u := by
  induction p with
  | nil => simp [mul]
  | cons t rest ih =>
    simp only [mul, List.foldr_cons, eval_add, eval_multiplyTerm, eval_cons] at *
    rw [ih]
    ring

@[simp] theorem eval_constant (a : ℚ) (s u : ℝ) : eval (constant a) s u = a := by
  simp [constant, termEval]

@[simp] theorem eval_time (s u : ℝ) : eval time s u = s := by
  simp [time, termEval]

@[simp] theorem eval_parameter (s u : ℝ) : eval parameter s u = u := by
  simp [parameter, termEval]

@[simp] theorem eval_power (p : Poly) (n : Nat) (s u : ℝ) :
    eval (power p n) s u = eval p s u ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ, mul_comm]

@[simp] theorem eval_sum (ps : List Poly) (s u : ℝ) :
    eval (sum ps) s u = (ps.map (fun p => eval p s u)).sum := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change eval (add p (sum rest)) s u = _
    simp only [eval_add, List.map_cons, List.sum_cons, ih]

@[simp] theorem eval_finSum {n : Nat} (p : Fin n → Poly) (s u : ℝ) :
    eval (finSum p) s u = ∑ i, eval (p i) s u := by
  simp [finSum, List.map_ofFn, List.sum_ofFn]

theorem eval_zero_of_all (p : Poly) (h : (p.all fun t => t.coefficient == 0) = true)
    (s u : ℝ) : eval p s u = 0 := by
  induction p with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, ih h.2, termEval]

/-- The checker may be run with `decide +kernel`; no native evaluator is trusted. -/
theorem eval_eq_of_equivalent {p q : Poly} (h : equivalent p q = true) (s u : ℝ) :
    eval p s u = eval q s u := by
  have hz := eval_zero_of_all (add p (neg q)) h s u
  simp only [eval_add, eval_neg] at hz
  linarith

#print axioms eval_eq_of_equivalent
end Gimle.Forseti.RationalPolynomial
