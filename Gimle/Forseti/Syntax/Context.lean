import Gimle.Forseti.Syntax

/-! Ordered variable contexts for formulas.

A `Formula n` addresses its coordinates by position alone. That is enough for
its semantics, but not for talking to anything outside Lean: a solver answers
with *its* variable names, and nothing ties those names to positions except a
convention in the caller.

A `Context` is that tie, made explicit and checked. It is an ordered list of
distinct, non-blank names; position `i` of a formula over it is the coordinate
named `names[i]`, and the dimension is the list's length, never supplied
separately. `NamedFormula` pairs a bare formula with its context. It is a
wrapper rather than an index on `Formula`, so `Formula` keeps its uniform index,
its eliminators and its derived `DecidableEq`.

Coordinates are written by name too: `Context.var` looks a name up, and the
lookup is checked when the formula is built. (Numerals on `Fin c.dimension`
are deliberately not provided: they would wrap modulo the dimension, so a
mistyped index would silently mean another coordinate.) `Goal` puts both sides
of an entailment over one context.

Names are checked only to be distinct and non-empty. Whether a name is a legal
identifier for some solver is that solver adapter's concern.

Answers come back by name: `Context.read` turns a named assignment into a point,
refusing a missing, repeated or unknown name, and `Context.read_mem` proves that
every coordinate of the point it returns is the value the answer gave that
coordinate's name. `Context.read_assign` is the round trip.

**No authority is granted here.** A context names coordinates; it proves
nothing about any formula.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Forseti

/-- Why a context, a named formula or a named answer was rejected. -/
inductive ContextError where
  /-- A context names no coordinate. -/
  | empty
  /-- The name at this position is the empty string. -/
  | blankName (position : Nat)
  /-- This name appears more than once. -/
  | duplicateName (name : String)
  /-- A formula's dimension differs from the number of names in its context. -/
  | dimensionMismatch (formula context : Nat)
  /-- An answer does not assign this coordinate. -/
  | missingName (name : String)
  /-- An answer assigns this coordinate more than once. -/
  | repeatedName (name : String)
  /-- An answer assigns a name the context does not have. -/
  | unknownName (name : String)
  /-- Two formulas meant to share a context have different ones. -/
  | contextMismatch
  deriving Repr, DecidableEq

/-- An ordered context of distinct, non-blank coordinate names. -/
structure Context where
  /-- The names, in coordinate order. -/
  names : List String
  nonempty : names ≠ []
  distinct : names.Nodup
  nonblank : ∀ name ∈ names, name ≠ ""

namespace Context

/-- Two contexts are equal exactly when they name the same coordinates in the
same order. -/
theorem ext_iff' {a b : Context} : a = b ↔ a.names = b.names := by
  constructor
  · rintro rfl; rfl
  · intro same
    cases a; cases b
    cases same
    rfl

instance : DecidableEq Context := fun a b =>
  decidable_of_iff (a.names = b.names) ext_iff'.symm

/-- The dimension a context fixes: one coordinate per name. -/
def dimension (context : Context) : Nat := context.names.length

/-- The name of a coordinate. -/
def name (context : Context) (coordinate : Fin context.dimension) : String :=
  context.names.get coordinate

/-- Build a context, rejecting an empty list, a blank name or a repeated name. -/
def make (names : List String) : Except ContextError Context :=
  if empty : names = [] then .error .empty
  else if nonblank : ∀ name ∈ names, name ≠ "" then
    if distinct : names.Nodup then .ok ⟨names, empty, distinct, nonblank⟩
    else
      .error (.duplicateName ((names.find? fun name => 1 < names.count name).getD ""))
  else .error (.blankName (names.findIdx (· == "")))

/-- A context that was built has exactly the names it was built from. -/
theorem make_names {names : List String} {context : Context}
    (built : make names = .ok context) : context.names = names := by
  unfold make at built
  split at built
  · cases built
  · split at built
    · split at built
      · cases built; rfl
      · cases built
    · cases built

/-- Names determine coordinates: no two coordinates share a name. -/
theorem name_injective (context : Context) : Function.Injective context.name :=
  fun _ _ same => Fin.ext (context.distinct.get_inj_iff.mp same |> congrArg Fin.val)

/-- The coordinate a name refers to, if the context has it. -/
def position? (context : Context) (name : String) : Option (Fin context.dimension) :=
  if bound : context.names.idxOf name < context.dimension then
    some ⟨context.names.idxOf name, bound⟩
  else none

/-- A position found for a name is the coordinate with that name. -/
theorem name_of_position? {context : Context} {name : String}
    {coordinate : Fin context.dimension}
    (found : context.position? name = some coordinate) :
    context.name coordinate = name := by
  unfold position? at found
  split at found
  · cases found
    exact List.idxOf_get _
  · cases found

/-- Every coordinate is found again by its own name. -/
theorem position?_name (context : Context) (coordinate : Fin context.dimension) :
    context.position? (context.name coordinate) = some coordinate := by
  have bound : context.names.idxOf (context.name coordinate) < context.dimension :=
    List.idxOf_lt_length_of_mem (List.get_mem _ _)
  unfold position?
  rw [dif_pos bound]
  congr 1
  exact context.name_injective (List.idxOf_get _)

/-- The coordinate a name refers to. The lookup is discharged when the formula
is built, by default with `decide`, so a misspelt name fails to compile. -/
def coordinate (context : Context) (name : String)
    (found : (context.position? name).isSome := by decide) : Fin context.dimension :=
  (context.position? name).get found

/-- The coordinate looked up by name has that name. -/
theorem name_coordinate (context : Context) (name : String)
    (found : (context.position? name).isSome) :
    context.name (context.coordinate name found) = name :=
  name_of_position? (Option.some_get found).symm

/-- A polynomial variable, by name. -/
def var (context : Context) (name : String)
    (found : (context.position? name).isSome := by decide) :
    Gimle.Asgard.Polynomial.Expr context.dimension :=
  .var (context.coordinate name found)

/-! ### Named answers -/

/-- An answer as a solver reports it: a value for each coordinate, by name. -/
abbrev Assignment := List (String × ℚ)

/-- Name a rational point, one entry per coordinate in context order. -/
def assign (context : Context) (point : Fin context.dimension → ℚ) : Assignment :=
  List.ofFn fun coordinate => (context.name coordinate, point coordinate)

/-- How many entries of an answer give a value for this name. -/
def occurrences (answer : Assignment) (name : String) : Nat :=
  answer.countP fun entry => entry.1 == name

/-- The value an answer gives a name, if any. -/
def valueOf (answer : Assignment) (name : String) : Option ℚ :=
  (answer.find? fun entry => entry.1 == name).map Prod.snd

/-- Read an answer back as a point. It must name every coordinate exactly once
and nothing else. -/
def read (context : Context) (answer : Assignment) :
    Except ContextError (Fin context.dimension → ℚ) :=
  match answer.find? (fun entry => !context.names.contains entry.1) with
  | some entry => .error (.unknownName entry.1)
  | none =>
      match context.names.find? (fun name => occurrences answer name != 1) with
      | some name =>
          .error (if occurrences answer name = 0 then .missingName name
            else .repeatedName name)
      | none => .ok fun coordinate => (valueOf answer (context.name coordinate)).getD 0

/-- Every coordinate of a point read from an answer is the value the answer gave
that coordinate's name, so no convention outside the context decides which is
which. -/
theorem read_mem {context : Context} {answer : Assignment}
    {point : Fin context.dimension → ℚ} (read_ok : context.read answer = .ok point)
    (coordinate : Fin context.dimension) :
    (context.name coordinate, point coordinate) ∈ answer := by
  unfold read at read_ok
  split at read_ok
  · cases read_ok
  · split at read_ok
    · cases read_ok
    · rename_i none_bad
      cases read_ok
      have once : occurrences answer (context.name coordinate) = 1 := by
        have := List.find?_eq_none.mp none_bad (context.name coordinate)
          (List.get_mem _ _)
        simpa using this
      have present :
          (answer.find? fun entry => entry.1 == context.name coordinate).isSome := by
        rw [List.find?_isSome]
        have positive :
            0 < answer.countP fun entry => entry.1 == context.name coordinate := by
          rw [occurrences] at once; omega
        obtain ⟨entry, member, hit⟩ := List.countP_pos_iff.mp positive
        exact ⟨entry, member, hit⟩
      obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp present
      have member := List.mem_of_find?_eq_some found
      have named : entry.1 = context.name coordinate := by
        simpa using List.find?_some found
      simp only [valueOf, found, Option.map_some, Option.getD_some]
      rw [← named]
      exact member

/-- Naming a point and reading the answer back gives the same point. -/
theorem read_assign (context : Context) (point : Fin context.dimension → ℚ) :
    context.read (context.assign point) = .ok point := by
  have firsts : (context.assign point).map Prod.fst = context.names := by
    simp only [assign, name, List.map_ofFn, Function.comp_def, List.get_eq_getElem]
    exact List.ofFn_getElem
  have once : ∀ name ∈ context.names, occurrences (context.assign point) name = 1 := by
    intro name member
    have counted := congrArg (List.countP (· == name)) firsts
    rw [List.countP_map] at counted
    have single := List.count_eq_one_of_mem context.distinct member
    rw [List.count] at single
    simpa [occurrences, Function.comp_def] using counted.trans single
  unfold read
  have known :
      (context.assign point).find? (fun entry => !context.names.contains entry.1) =
        none := by
    apply List.find?_eq_none.mpr
    intro entry member
    have : entry.1 ∈ context.names := by
      rw [← firsts]; exact List.mem_map_of_mem member
    simpa using this
  rw [known]
  simp only
  have counted :
      context.names.find? (fun name => occurrences (context.assign point) name != 1) =
        none := by
    apply List.find?_eq_none.mpr
    intro name member
    simp [once name member]
  rw [counted]
  simp only [Except.ok.injEq]
  funext coordinate
  have entry_mem :
      (context.name coordinate, point coordinate) ∈ context.assign point := by
    simp only [assign, List.mem_ofFn]
    exact ⟨coordinate, rfl⟩
  have present : ((context.assign point).find?
      fun entry => entry.1 == context.name coordinate).isSome := by
    rw [List.find?_isSome]
    exact ⟨_, entry_mem, by simp⟩
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp present
  have member := List.mem_of_find?_eq_some found
  have named : entry.1 = context.name coordinate := by simpa using List.find?_some found
  simp only [assign, List.mem_ofFn] at member
  obtain ⟨other, rfl⟩ := member
  have same : other = coordinate := context.name_injective named
  subst same
  simp [valueOf, found]

/-! ### Concatenation -/

/-- Place one context's coordinates after another's, rejecting a name the two
share. -/
def append (left right : Context) : Except ContextError Context :=
  make (left.names ++ right.names)

/-- A concatenated context has one coordinate per coordinate of its parts. -/
theorem append_dimension {left right joined : Context}
    (joined_ok : left.append right = .ok joined) :
    joined.dimension = left.dimension + right.dimension := by
  simp [dimension, make_names joined_ok]

/-- The left part's coordinates keep their names, in their positions. -/
theorem append_name_left {left right joined : Context}
    (joined_ok : left.append right = .ok joined) (coordinate : Fin left.dimension) :
    joined.name (Fin.cast (append_dimension joined_ok).symm
      (Fin.castAdd right.dimension coordinate)) = left.name coordinate := by
  have names := make_names joined_ok
  simp only [name, List.get_eq_getElem, Fin.val_cast, Fin.val_castAdd]
  simp only [names]
  exact List.getElem_append_left _

/-- The right part's coordinates keep their names, after the left part's. -/
theorem append_name_right {left right joined : Context}
    (joined_ok : left.append right = .ok joined) (coordinate : Fin right.dimension) :
    joined.name (Fin.cast (append_dimension joined_ok).symm
      (Fin.natAdd left.dimension coordinate)) = right.name coordinate := by
  have names := make_names joined_ok
  simp only [name, List.get_eq_getElem, Fin.val_cast, Fin.val_natAdd]
  simp only [names]
  rw [List.getElem_append_right (by simp [dimension])]
  simp [dimension]

end Context

/-! ### Formulas over a named context -/

/-- Read a formula at another dimension that is provably equal. -/
def Formula.cast {source target : Nat} (same : source = target)
    (formula : Formula source) : Formula target :=
  same ▸ formula

/-- A cast formula holds where the original does, at the recast point. -/
@[simp] theorem Formula.holds_cast {source target : Nat} (same : source = target)
    (formula : Formula source) (point : Point target) :
    (formula.cast same).holds point ↔
      formula.holds (fun i => point (Fin.cast same i)) := by
  subst same
  rfl

/-- A formula together with the ordered context naming its coordinates. The
dimension is the context's; there is no second, independent one. -/
structure NamedFormula where
  /-- The coordinates, by name and in order. -/
  context : Context
  /-- The formula, over exactly those coordinates. -/
  formula : Formula context.dimension

/-- Two named formulas are equal exactly when their contexts and their formulas
are. The same shape over different names is a different named formula. -/
theorem NamedFormula.ext_iff' {a b : NamedFormula} :
    a = b ↔ ∃ same : a.context = b.context,
      a.formula.cast (congrArg Context.dimension same) = b.formula := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨same, formulas⟩
    cases a; cases b
    cases same
    cases formulas
    rfl

instance : DecidableEq NamedFormula := fun a b =>
  if same : a.context = b.context then
    decidable_of_iff (a.formula.cast (congrArg Context.dimension same) = b.formula)
      (by
        rw [NamedFormula.ext_iff']
        exact ⟨fun h => ⟨same, h⟩, fun ⟨_, h⟩ => h⟩)
  else isFalse fun equal => same (congrArg NamedFormula.context equal)

namespace NamedFormula

/-- Pair a formula with a context, rejecting a dimension that differs from the
number of names. -/
def make (context : Context) {dimension : Nat} (formula : Formula dimension) :
    Except ContextError NamedFormula :=
  if same : dimension = context.dimension then .ok ⟨context, formula.cast same⟩
  else .error (.dimensionMismatch dimension context.dimension)

/-- The set a named formula denotes, over its own coordinates. -/
def holds (named : NamedFormula) (point : Point named.context.dimension) : Prop :=
  named.formula.holds point

/-- Constrain the left coordinates with one named formula and the right with
another, over the concatenated context. Shared names are rejected, so a
coordinate can never silently mean two things. -/
def product (first second : NamedFormula) : Except ContextError NamedFormula :=
  match joined : first.context.append second.context with
  | .error failure => .error failure
  | .ok context =>
      .ok ⟨context, (first.formula.product second.formula).cast
        (Context.append_dimension joined).symm⟩

/-- A product's context is the concatenation of its factors' contexts. -/
theorem product_context {first second joined : NamedFormula}
    (product_ok : first.product second = .ok joined) :
    first.context.append second.context = .ok joined.context := by
  unfold product at product_ok
  split at product_ok
  · cases product_ok
  · rename_i context agree
    cases product_ok
    exact agree

/-- A product holds exactly where each factor holds on its own block of
coordinates: the left factor on the first positions, the right on the rest.
`Context.append_name_left` and `append_name_right` say those positions carry
the factors' own names. -/
theorem holds_product {first second joined : NamedFormula}
    (product_ok : first.product second = .ok joined)
    (point : Point joined.context.dimension) :
    joined.holds point ↔
      first.holds (fun i => point (Fin.cast
        (Context.append_dimension (product_context product_ok)).symm
          (Fin.castAdd second.context.dimension i))) ∧
      second.holds (fun i => point (Fin.cast
        (Context.append_dimension (product_context product_ok)).symm
          (Fin.natAdd first.context.dimension i))) := by
  unfold product at product_ok
  split at product_ok
  · cases product_ok
  · cases product_ok
    simp only [holds, Formula.holds_cast, Formula.holds_product]
    rfl

end NamedFormula

/-! ### Entailment goals over one context -/

/-- Both sides of an entailment question, over one ordered context. This is the
form a checker binds: a certificate or counterexample is checked against the
goal's own formulas and names, never against a claimed statement. -/
structure Goal where
  /-- The coordinates both formulas are about. -/
  context : Context
  /-- What is assumed. -/
  antecedent : Formula context.dimension
  /-- What is claimed to follow. -/
  consequent : Formula context.dimension

namespace Goal

/-- The entailment the goal asks about. -/
def Entailment (goal : Goal) : Prop :=
  FormulaEntailment goal.antecedent goal.consequent

/-- Pose a goal from two named formulas, which must share their context exactly:
the same names in the same order. -/
def ofNamed (antecedent consequent : NamedFormula) : Except ContextError Goal :=
  if same : antecedent.context = consequent.context then
    .ok ⟨antecedent.context, antecedent.formula,
      consequent.formula.cast (congrArg Context.dimension same).symm⟩
  else .error .contextMismatch

/-- A goal posed from named formulas asks exactly about those formulas. -/
theorem ofNamed_entailment {antecedent consequent : NamedFormula} {goal : Goal}
    (posed : ofNamed antecedent consequent = .ok goal) :
    ∃ same : antecedent.context = consequent.context,
      goal.context = antecedent.context ∧
      (goal.Entailment ↔ ∀ point, antecedent.holds point →
        consequent.holds fun i => point (Fin.cast
          (congrArg Context.dimension same).symm i)) := by
  unfold ofNamed at posed
  split at posed
  · rename_i same
    cases posed
    refine ⟨same, rfl, ?_⟩
    simp only [Entailment, FormulaEntailment, NamedFormula.holds, Formula.holds_cast]
  · cases posed

end Goal

#print axioms Context.read_mem
#print axioms Context.read_assign
#print axioms Context.append_name_left
#print axioms Context.append_name_right
#print axioms NamedFormula.holds_product

end Gimle.Forseti.Syntax
