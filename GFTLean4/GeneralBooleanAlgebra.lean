/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralSemantics

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false

/-
  Boolean algebra of general fault trees.

  This file proves the basic semantic laws satisfied by the
  executable semantics of general fault trees.
-/

namespace GFTree

variable {Event : Type} [DecidableEq Event]

/-
===========================================================
1. Double Negation
===========================================================
-/

/--
NOT (NOT A) is semantically equivalent to A.
-/
theorem double_negation
    (t : GFTree Event) :
    SemEquiv (NOT (NOT t)) t := by
  intro C
  simp [eval_NOT]

/-
===========================================================
2. AND and OR Negation
===========================================================
-/

/--
NOT (A AND B) = NAND(A,B)
-/
theorem Negation_AND
    (ts : List (GFTree Event)) :
    SemEquiv (NOT (AND ts)) (NAND ts) := by
  intro C
  simp [eval_NOT, eval_AND, eval_NAND]

/--
NOT (A OR B) = NOR(A,B)
-/
theorem Negation_OR
    (ts : List (GFTree Event)) :
    SemEquiv (NOT (OR ts)) (NOR ts) := by
  intro C
  simp [eval_NOT, eval_OR, eval_NOR]

/-
===========================================================
3. NAND/NOR Characterizations
===========================================================
-/

/--
NAND is the negation of conjunction.
-/
theorem nand_characterization
    (ts : List (GFTree Event)) :
    ∀ C,
      eval C (NAND ts) =
      !(eval C (AND ts)) := by
  intro C
  simp

/--
NOR is the negation of disjunction.
-/
theorem nor_characterization
    (ts : List (GFTree Event)) :
    ∀ C,
      eval C (NOR ts) =
      !(eval C (OR ts)) := by
  intro C
  simp

/-
===========================================================
4. Idempotence
===========================================================
-/

/--
AND(A,A)=A
-/
theorem and_idempotent
    (t : GFTree Event) :
    SemEquiv
      (AND [t,t])
      t := by
  intro C
  simp [eval_AND]

/--
OR(A,A)=A
-/
theorem or_idempotent
    (t : GFTree Event) :
    SemEquiv
      (OR [t,t])
      t := by
  intro C
  simp [eval_OR]

/-
===========================================================
5. Commutativity
===========================================================
-/

/--
AND is commutative.
-/
theorem and_comm
    (a b : GFTree Event) :
    SemEquiv
      (AND [a,b])
      (AND [b,a]) := by
  intro C
  simp [eval_AND]
  cases hA : eval C a <;> cases hB : eval C b <;> simp

/--
OR is commutative.
-/
theorem or_comm
    (a b : GFTree Event) :
    SemEquiv
      (OR [a,b])
      (OR [b,a]) := by
  intro C
  simp [eval_OR]
  cases hA : eval C a <;> cases hB : eval C b <;> simp

/-
===========================================================
6. Associativity
===========================================================
-/

/--
AND is associative.
-/
theorem and_assoc
    (a b c : GFTree Event) :
    SemEquiv
      (AND [AND [a,b], c])
      (AND [a, AND [b,c]]) := by
  intro C
  simp [eval_AND]
  cases hA : eval C a <;>
  cases hB : eval C b <;>
  cases hC : eval C c <;>
  simp

/--
OR is associative.
-/
theorem or_assoc
    (a b c : GFTree Event) :
    SemEquiv
      (OR [OR [a,b], c])
      (OR [a, OR [b,c]]) := by
  intro C
  simp [eval_OR]
  cases hA : eval C a <;>
  cases hB : eval C b <;>
  cases hC : eval C c <;>
  simp

/-
===========================================================
7. Absorption
===========================================================
-/

/--
A OR (A AND B) = A
-/
theorem absorption_OR
    (a b : GFTree Event) :
    SemEquiv
      (OR [a, AND [a,b]])
      a := by
  intro C
  simp [eval_AND, eval_OR]
  cases hA : eval C a <;> cases hB : eval C b <;> simp

/--
A AND (A OR B)=A
-/
theorem absorption_AND
    (a b : GFTree Event) :
    SemEquiv
      (AND [a, OR [a,b]])
      a := by
  intro C
  simp [eval_AND, eval_OR]
  cases hA : eval C a <;> cases hB : eval C b <;> simp

end GFTree
