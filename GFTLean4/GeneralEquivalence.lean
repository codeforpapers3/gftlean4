/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralPositive

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false


/-!
  Semantic equivalence and preservation results for general fault trees.

  This file strengthens the semantic-foundation layer of the framework.
  It proves that positive fault trees are semantically identical to their
  underlying general fault trees and that semantic equivalence preserves
  evaluation, cut-set satisfaction, positivity-derived monotonicity, and
  common Boolean transformations.
-/

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Semantic Equivalence Basics
===========================================================
-/

/-- Semantic equivalence preserves evaluation. -/
theorem SemEquiv.eval_eq [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (h : SemEquiv t₁ t₂)
    (C : CutSet Event) :
    eval C t₁ = eval C t₂ := by
  exact h C

/-- Semantic equivalence preserves cut-set satisfaction. -/
theorem SemEquiv.isCutSet_iff [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (h : SemEquiv t₁ t₂)
    (C : CutSet Event) :
    IsCutSet C t₁ ↔ IsCutSet C t₂ := by
  unfold IsCutSet
  rw [h C]

/-
===========================================================
2. Positive-Tree Semantic Preservation
===========================================================
-/

namespace PositiveTree

/--
Evaluation of a positive fault tree is exactly evaluation of its
underlying general fault tree.
-/
theorem eval_eq_general [DecidableEq Event]
    (C : CutSet Event)
    (t : PositiveTree Event) :
    PositiveTree.eval C t =
      GFTree.eval C (t : GFTree Event) := by
  rfl

/--
A positive fault tree is semantically equivalent to its underlying
general fault tree.
-/
theorem semEquiv_general [DecidableEq Event]
    (t : PositiveTree Event) :
    SemEquiv (t : GFTree Event) t.tree := by
  intro C
  rfl

/--
The positive-tree constructor `ofGeneral` preserves evaluation.
-/
theorem eval_ofGeneral [DecidableEq Event]
    (C : CutSet Event)
    (t : GFTree Event)
    (h : Positive t) :
    PositiveTree.eval C (PositiveTree.ofGeneral t h) =
      GFTree.eval C t := by
  rfl

/--
The positive-tree constructor `ofGeneral` is semantically equivalent
to the original general tree.
-/
theorem ofGeneral_semEquiv [DecidableEq Event]
    (t : GFTree Event)
    (h : Positive t) :
    SemEquiv
      ((PositiveTree.ofGeneral t h : PositiveTree Event) : GFTree Event)
      t := by
  intro C
  rfl

/--
Cut-set satisfaction for a positive tree is the same as satisfaction
for its underlying general tree.
-/
theorem isCutSet_iff_general [DecidableEq Event]
    (C : CutSet Event)
    (t : PositiveTree Event) :
    IsCutSet C (t : GFTree Event) ↔
      GFTree.eval C (t : GFTree Event) = true := by
  rfl

/--
Every positive tree inherits monotonicity from the general positive-fragment
metatheorem.
-/
theorem monotone_of_positive [DecidableEq Event]
    (t : PositiveTree Event) :
    Monotone (t : GFTree Event) := by
  exact PositiveTree.monotone t

end PositiveTree

/-
===========================================================
3. Semantic Equivalence Preserves Monotonicity
===========================================================
-/

/--
If two trees are semantically equivalent, monotonicity transfers from
the first tree to the second.
-/
theorem SemEquiv.monotone_of_left [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (hEq : SemEquiv t₁ t₂)
    (hMono : Monotone t₁) :
    Monotone t₂ := by
  intro C₁ C₂ hSub hEval
  have hEval₁ : eval C₁ t₁ = true := by
    rw [hEq C₁]
    exact hEval
  have hEval₂ : eval C₂ t₁ = true := by
    exact hMono C₁ C₂ hSub hEval₁
  rw [← hEq C₂]
  exact hEval₂

/--
If two trees are semantically equivalent, monotonicity transfers from
the second tree to the first.
-/
theorem SemEquiv.monotone_of_right [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (hEq : SemEquiv t₁ t₂)
    (hMono : Monotone t₂) :
    Monotone t₁ := by
  exact hEq.symm.monotone_of_left hMono

/--
Semantic equivalence preserves monotonicity in both directions.
-/
theorem SemEquiv.monotone_iff [DecidableEq Event]
    {t₁ t₂ : GFTree Event}
    (hEq : SemEquiv t₁ t₂) :
    Monotone t₁ ↔ Monotone t₂ := by
  constructor
  · intro h
    exact hEq.monotone_of_left h
  · intro h
    exact hEq.monotone_of_right h

/-
===========================================================
4. Instantiated Boolean Equivalence Results
===========================================================
-/

/-- Double negation preserves evaluation for every cut set. -/
theorem eval_double_negation [DecidableEq Event]
    (C : CutSet Event)
    (t : GFTree Event) :
    eval C (NOT (NOT t)) = eval C t := by
  exact double_negation t C

/-- De Morgan equivalence for AND gates, instantiated at evaluation level. -/
theorem eval_Negation_AND [DecidableEq Event]
    (C : CutSet Event)
    (ts : List (GFTree Event)) :
    eval C (NOT (AND ts)) = eval C (NAND ts) := by
  exact Negation_AND ts C

/-- De Morgan equivalence for OR gates, instantiated at evaluation level. -/
theorem eval_Negation_OR [DecidableEq Event]
    (C : CutSet Event)
    (ts : List (GFTree Event)) :
    eval C (NOT (OR ts)) = eval C (NOR ts) := by
  exact Negation_OR ts C

/-- AND commutativity preserves evaluation. -/
theorem eval_AND_comm [DecidableEq Event]
    (C : CutSet Event)
    (a b : GFTree Event) :
    eval C (AND [a, b]) = eval C (AND [b, a]) := by
  exact and_comm a b C

/-- OR commutativity preserves evaluation. -/
theorem eval_OR_comm [DecidableEq Event]
    (C : CutSet Event)
    (a b : GFTree Event) :
    eval C (OR [a, b]) = eval C (OR [b, a]) := by
  exact or_comm a b C

/-- AND associativity preserves evaluation. -/
theorem eval_AND_assoc [DecidableEq Event]
    (C : CutSet Event)
    (a b c : GFTree Event) :
    eval C (AND [AND [a, b], c]) =
      eval C (AND [a, AND [b, c]]) := by
  exact and_assoc a b c C

/-- OR associativity preserves evaluation. -/
theorem eval_OR_assoc [DecidableEq Event]
    (C : CutSet Event)
    (a b c : GFTree Event) :
    eval C (OR [OR [a, b], c]) =
      eval C (OR [a, OR [b, c]]) := by
  exact or_assoc a b c C

/-- AND idempotence preserves evaluation. -/
theorem eval_AND_idempotent [DecidableEq Event]
    (C : CutSet Event)
    (t : GFTree Event) :
    eval C (AND [t, t]) = eval C t := by
  exact and_idempotent t C

/-- OR idempotence preserves evaluation. -/
theorem eval_OR_idempotent [DecidableEq Event]
    (C : CutSet Event)
    (t : GFTree Event) :
    eval C (OR [t, t]) = eval C t := by
  exact or_idempotent t C

/-- OR absorption preserves evaluation. -/
theorem eval_absorption_OR [DecidableEq Event]
    (C : CutSet Event)
    (a b : GFTree Event) :
    eval C (OR [a, AND [a, b]]) = eval C a := by
  exact absorption_OR a b C

/-- AND absorption preserves evaluation. -/
theorem eval_absorption_AND [DecidableEq Event]
    (C : CutSet Event)
    (a b : GFTree Event) :
    eval C (AND [a, OR [a, b]]) = eval C a := by
  exact absorption_AND a b C

end GFTree
