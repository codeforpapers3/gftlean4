/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralMonotonicity

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false

/-
  Positive fault trees as a formally defined fragment of general fault trees.

  A positive fault tree is represented as a structure containing:
  * an underlying general fault tree;
  * a proof that this tree satisfies the `Positive` predicate.

  Thus, positive fault trees are not a separate syntax, but a formally
  specified sublanguage of general fault trees.
-/

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Positive Fault Trees
===========================================================
-/

/-- A positive fault tree is a general fault tree equipped with a proof of positivity. -/
structure PositiveTree (Event : Type) where
  tree : GFTree Event
  positive : Positive tree

namespace PositiveTree

/-- Coerce a positive fault tree to its underlying general fault tree. -/
instance : Coe (PositiveTree Event) (GFTree Event) where
  coe t := t.tree

/-- The underlying general fault tree of a positive fault tree. -/
def toTree (t : PositiveTree Event) : GFTree Event :=
  t.tree

/-- Every positive fault tree satisfies the `Positive` predicate. -/
theorem isPositive (t : PositiveTree Event) :
    Positive (t : GFTree Event) := by
  exact t.positive

/-- Build a positive fault tree from a general tree and a proof of positivity. -/
def ofGeneral (t : GFTree Event) (h : Positive t) : PositiveTree Event :=
  ⟨t, h⟩

/-- The underlying tree of `ofGeneral` is the original tree. -/
@[simp]
theorem ofGeneral_toTree
    (t : GFTree Event) (h : Positive t) :
    (ofGeneral t h).toTree = t := by
  rfl

/-
===========================================================
2. Positive Constructors
===========================================================
-/

/-- Construct a positive basic-event tree. -/
def PBE (e : Event) : PositiveTree Event :=
  ⟨BE e, by
    simp [BE]
  ⟩

/-- Construct a positive AND tree from positive child trees. -/
def PAND (ts : List (PositiveTree Event)) : PositiveTree Event :=
by
  refine ⟨AND (ts.map PositiveTree.toTree), ?_⟩
  rw [positive_AND]
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, _hu, rfl⟩
  exact u.positive

/-- Construct a positive OR tree from positive child trees. -/
def POR (ts : List (PositiveTree Event)) : PositiveTree Event :=
by
  refine ⟨OR (ts.map PositiveTree.toTree), ?_⟩
  rw [positive_OR]
  intro t ht
  rcases List.mem_map.mp ht with ⟨u, _hu, rfl⟩
  exact u.positive
/-
===========================================================
3. Constructor Simplification Lemmas
===========================================================
-/

/-- The underlying tree of `PBE e` is `BE e`. -/
@[simp]
theorem PBE_toTree (e : Event) :
    (PBE e).toTree = BE e := by
  rfl

/-- Coercing `PBE e` gives `BE e`. -/
@[simp]
theorem coe_PBE (e : Event) :
    ((PBE e : PositiveTree Event) : GFTree Event) = BE e := by
  rfl

/-- The underlying tree of `PAND ts` is an AND of the underlying children. -/
@[simp]
theorem PAND_toTree (ts : List (PositiveTree Event)) :
    (PAND ts).toTree =
      AND (ts.map PositiveTree.toTree) := by
  rfl

/-- Coercing `PAND ts` gives an AND of the underlying children. -/
@[simp]
theorem coe_PAND (ts : List (PositiveTree Event)) :
    ((PAND ts : PositiveTree Event) : GFTree Event) =
      AND (ts.map PositiveTree.toTree) := by
  rfl

/-- The underlying tree of `POR ts` is an OR of the underlying children. -/
@[simp]
theorem POR_toTree (ts : List (PositiveTree Event)) :
    (POR ts).toTree =
      OR (ts.map PositiveTree.toTree) := by
  rfl

/-- Coercing `POR ts` gives an OR of the underlying children. -/
@[simp]
theorem coe_POR (ts : List (PositiveTree Event)) :
    ((POR ts : PositiveTree Event) : GFTree Event) =
      OR (ts.map PositiveTree.toTree) := by
  rfl

/-
===========================================================
4. Semantics of Positive Fault Trees
===========================================================
-/

/-- Evaluate a positive fault tree using the general fault-tree semantics. -/
def eval [DecidableEq Event]
    (C : CutSet Event) (t : PositiveTree Event) : Bool :=
  GFTree.eval C (t : GFTree Event)

/-- Evaluation of a positive basic-event tree. -/
@[simp]
theorem eval_PBE [DecidableEq Event]
    (C : CutSet Event) (e : Event) :
    eval C (PBE e) = decide (e ∈ C) := by
  simp [eval, PBE, BE]

/-- Evaluation of a positive AND tree. -/
@[simp]
theorem eval_PAND [DecidableEq Event]
    (C : CutSet Event) (ts : List (PositiveTree Event)) :
    eval C (PAND ts) =
      evalAll C (ts.map PositiveTree.toTree) := by
  rfl

/-- Evaluation of a positive OR tree. -/
@[simp]
theorem eval_POR [DecidableEq Event]
    (C : CutSet Event) (ts : List (PositiveTree Event)) :
    eval C (POR ts) =
      evalAny C (ts.map PositiveTree.toTree) := by
  rfl

/-
===========================================================
5. Monotonicity
===========================================================
-/

/-- Every positive fault tree is monotone under the general semantics. -/
theorem monotone [DecidableEq Event]
    (t : PositiveTree Event) :
    Monotone (t : GFTree Event) := by
  exact positive_monotone (t : GFTree Event) t.positive

/-- The positive-fault-tree fragment is monotone. -/
theorem fragment_monotone [DecidableEq Event]
    (t : PositiveTree Event) :
    Monotone (t : GFTree Event) := by
  exact monotone t

/-
===========================================================
6. Basic Examples
===========================================================
-/

/-- A positive AND of two basic events. -/
def exampleAND (a b : Event) : PositiveTree Event :=
  PAND [PBE a, PBE b]

/-- A positive OR of two basic events. -/
def exampleOR (a b : Event) : PositiveTree Event :=
  POR [PBE a, PBE b]

/-- The example positive AND tree is monotone. -/
theorem exampleAND_monotone [DecidableEq Event]
    (a b : Event) :
    Monotone ((exampleAND a b : PositiveTree Event) : GFTree Event) := by
  exact monotone (exampleAND a b)

/-- The example positive OR tree is monotone. -/
theorem exampleOR_monotone [DecidableEq Event]
    (a b : Event) :
    Monotone ((exampleOR a b : PositiveTree Event) : GFTree Event) := by
  exact monotone (exampleOR a b)

end PositiveTree

end GFTree
