/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralProperties

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false

/-
  Executable semantics of general fault trees.

  This file defines Boolean evaluation of general fault trees,
  semantic cut sets, and basic semantic simplification lemmas.
-/

namespace GFTree

variable {Event : Type}

/--
A finite set of failed basic events used as an input configuration
to the executable semantics.

Despite the implementation name `CutSet`, a value of this type need
not satisfy a particular fault tree. Semantic satisfaction is defined
separately by `IsCutSet`.
-/
abbrev CutSet (Event : Type) := Finset Event

/-
===========================================================
1. Executable Boolean Semantics
===========================================================
-/

mutual

/-- Evaluate a general fault tree under an active cut set `C`. -/
def eval [DecidableEq Event] (C : CutSet Event) : GFTree Event → Bool
  | basic e =>
      decide (e ∈ C)

  | gate GGate.andGate ts =>
      evalAll C ts

  | gate GGate.orGate ts =>
      evalAny C ts

  | gate GGate.notGate ts =>
      match ts with
      | [t] => !(eval C t)
      | _ => false

  | gate GGate.nandGate ts =>
      !(evalAll C ts)

  | gate GGate.norGate ts =>
      !(evalAny C ts)

/-- Evaluate whether all trees in a list evaluate to true. -/
def evalAll [DecidableEq Event] (C : CutSet Event) :
    List (GFTree Event) → Bool
  | [] => true
  | t :: ts => eval C t && evalAll C ts

/-- Evaluate whether at least one tree in a list evaluates to true. -/
def evalAny [DecidableEq Event] (C : CutSet Event) :
    List (GFTree Event) → Bool
  | [] => false
  | t :: ts => eval C t || evalAny C ts

end

/-
===========================================================
2. Semantic Cut Sets
===========================================================
-/

/--
`IsCutSet C t` means that activating all events in `C`
causes the top event of `t` to evaluate to true.
-/
def IsCutSet [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) : Prop :=
  eval C t = true

/-
===========================================================
3. Evaluation Simplification Lemmas
===========================================================
-/

/-- A basic event evaluates to true exactly when it belongs to the cut set. -/
@[simp]
theorem eval_basic [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    eval C (basic e) = decide (e ∈ C) := by
  simp [eval]

/-- An AND gate evaluates using `evalAll`. -/
@[simp]
theorem eval_andGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (gate GGate.andGate ts) = evalAll C ts := by
  simp [eval]

/-- An OR gate evaluates using `evalAny`. -/
@[simp]
theorem eval_orGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (gate GGate.orGate ts) = evalAny C ts := by
  simp [eval]

/-- A singleton NOT gate evaluates as Boolean negation of its child. -/
@[simp]
theorem eval_notGate_singleton [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) :
    eval C (gate GGate.notGate [t]) = !(eval C t) := by
  simp [eval]

/-- A malformed NOT gate evaluates to false. -/
@[simp]
theorem eval_notGate_empty [DecidableEq Event]
    (C : CutSet Event) :
    eval C (gate GGate.notGate ([] : List (GFTree Event))) = false := by
  simp [eval]

/-- A NAND gate evaluates as the negation of `evalAll`. -/
@[simp]
theorem eval_nandGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (gate GGate.nandGate ts) = !(evalAll C ts) := by
  simp [eval]

/-- A NOR gate evaluates as the negation of `evalAny`. -/
@[simp]
theorem eval_norGate [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (gate GGate.norGate ts) = !(evalAny C ts) := by
  simp [eval]

/-- The empty list evaluates to true under `evalAll`. -/
@[simp]
theorem evalAll_nil [DecidableEq Event]
    (C : CutSet Event) :
    evalAll C ([] : List (GFTree Event)) = true := by
  simp [evalAll]

/-- Evaluation of `evalAll` over a nonempty list. -/
@[simp]
theorem evalAll_cons [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) (ts : List (GFTree Event)) :
    evalAll C (t :: ts) = (eval C t && evalAll C ts) := by
  simp [evalAll]

/-- The empty list evaluates to false under `evalAny`. -/
@[simp]
theorem evalAny_nil [DecidableEq Event]
    (C : CutSet Event) :
    evalAny C ([] : List (GFTree Event)) = false := by
  simp [evalAny]

/-- Evaluation of `evalAny` over a nonempty list. -/
@[simp]
theorem evalAny_cons [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) (ts : List (GFTree Event)) :
    evalAny C (t :: ts) = (eval C t || evalAny C ts) := by
  simp [evalAny]

/-
===========================================================
4. Smart Constructor Evaluation Lemmas
===========================================================
-/

/-- A basic event smart constructor evaluates by membership in the cut set. -/
@[simp]
theorem eval_BE [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    eval C (BE e) = decide (e ∈ C) := by
  simp [BE]

/-- An AND smart constructor evaluates using `evalAll`. -/
@[simp]
theorem eval_AND [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (AND ts) = evalAll C ts := by
  simp [AND]

/-- An OR smart constructor evaluates using `evalAny`. -/
@[simp]
theorem eval_OR [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (OR ts) = evalAny C ts := by
  simp [OR]

/-- A NOT smart constructor evaluates as Boolean negation. -/
@[simp]
theorem eval_NOT [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) :
    eval C (NOT t) = !(eval C t) := by
  simp [NOT]

/-- A NAND smart constructor evaluates as negated conjunction. -/
@[simp]
theorem eval_NAND [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (NAND ts) = !(evalAll C ts) := by
  simp [NAND]

/-- A NOR smart constructor evaluates as negated disjunction. -/
@[simp]
theorem eval_NOR [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event)) :
    eval C (NOR ts) = !(evalAny C ts) := by
  simp [NOR]

/-
===========================================================
5. Basic Cut-Set Facts
===========================================================
-/

/-- A singleton cut set satisfies its own basic-event tree. -/
theorem singleton_is_cutset_basic [DecidableEq Event]
    (e : Event) :
    IsCutSet ({e} : CutSet Event) (basic e) := by
  simp [IsCutSet, eval]

/-- A cut set satisfies a basic-event tree iff the event belongs to it. -/
theorem isCutSet_basic_iff [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    IsCutSet C (basic e) ↔ e ∈ C := by
  simp [IsCutSet, eval]

/-- If the head and the tail of an AND list are satisfied, then the whole AND is satisfied. -/
theorem isCutSet_AND_cons [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) (ts : List (GFTree Event))
    (hHead : IsCutSet C t)
    (hTail : evalAll C ts = true) :
    IsCutSet C (AND (t :: ts)) := by
  unfold IsCutSet at hHead ⊢
  simp [eval_AND, evalAll, hHead, hTail]

/-- If one child of an OR gate is satisfied, then the whole OR gate is satisfied. -/
theorem isCutSet_OR_head [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event) (ts : List (GFTree Event))
    (h : IsCutSet C t) :
    IsCutSet C (OR (t :: ts)) := by
  unfold IsCutSet at h ⊢
  simp [eval_OR, evalAny, h]

/-- If a tree is not satisfied, then its NOT gate is satisfied. -/
theorem isCutSet_NOT_of_not_eval [DecidableEq Event]
    (C : CutSet Event) (t : GFTree Event)
    (h : eval C t = false) :
    IsCutSet C (NOT t) := by
  unfold IsCutSet
  simp [eval_NOT, h]

/-- If an AND-list is not satisfied, then the corresponding NAND gate is satisfied. -/
theorem isCutSet_NAND_of_not_evalAll [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event))
    (h : evalAll C ts = false) :
    IsCutSet C (NAND ts) := by
  unfold IsCutSet
  simp [eval_NAND, h]

/-- If an OR-list is not satisfied, then the corresponding NOR gate is satisfied. -/
theorem isCutSet_NOR_of_not_evalAny [DecidableEq Event]
    (C : CutSet Event) (ts : List (GFTree Event))
    (h : evalAny C ts = false) :
    IsCutSet C (NOR ts) := by
  unfold IsCutSet
  simp [eval_NOR, h]

/-
===========================================================
6. Semantic Equivalence
===========================================================
-/

/--
Two general fault trees are semantically equivalent if they evaluate
to the same Boolean value under every cut set.
-/
def SemEquiv [DecidableEq Event]
    (t₁ t₂ : GFTree Event) : Prop :=
  ∀ C : CutSet Event, eval C t₁ = eval C t₂

/-- Semantic equivalence is reflexive. -/
theorem SemEquiv.refl [DecidableEq Event]
    (t : GFTree Event) :
    SemEquiv t t := by
  intro C
  rfl

/-- Semantic equivalence is symmetric. -/
theorem SemEquiv.symm [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (h : SemEquiv t₁ t₂) :
    SemEquiv t₂ t₁ := by
  intro C
  exact (h C).symm

/-- Semantic equivalence is transitive. -/
theorem SemEquiv.trans [DecidableEq Event]
    {t₁ t₂ t₃ : GFTree Event}
    (h₁ : SemEquiv t₁ t₂)
    (h₂ : SemEquiv t₂ t₃) :
    SemEquiv t₁ t₃ := by
  intro C
  exact Eq.trans (h₁ C) (h₂ C)

end GFTree
