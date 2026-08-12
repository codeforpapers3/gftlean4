/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralSyntax

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false

/-
  Properties of general fault trees.

  This file introduces two important predicates:

    • WellFormed : syntactic well-formedness
    • Positive   : positive/coherent fragment

  together with simplification and inversion lemmas.
-/

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Well-Formedness
===========================================================
-/

/--
`WellFormed t` states that every gate satisfies its arity
constraints and every subtree is itself well formed.
-/
inductive WellFormed : GFTree Event → Prop

| basic (e : Event) :
    WellFormed (basic e)

| andGate
    (ts : List (GFTree Event))
    (hne : ts ≠ [])
    (hall : ∀ t ∈ ts, WellFormed t) :
    WellFormed (gate GGate.andGate ts)

| orGate
    (ts : List (GFTree Event))
    (hne : ts ≠ [])
    (hall : ∀ t ∈ ts, WellFormed t) :
    WellFormed (gate GGate.orGate ts)

| notGate
    (t : GFTree Event)
    (h : WellFormed t) :
    WellFormed (gate GGate.notGate [t])

| nandGate
    (ts : List (GFTree Event))
    (hne : ts ≠ [])
    (hall : ∀ t ∈ ts, WellFormed t) :
    WellFormed (gate GGate.nandGate ts)

| norGate
    (ts : List (GFTree Event))
    (hne : ts ≠ [])
    (hall : ∀ t ∈ ts, WellFormed t) :
    WellFormed (gate GGate.norGate ts)

/-
===========================================================
2. Positive Fragment
===========================================================
-/

/--
`Positive t` holds when `t` belongs to the positive fragment of
the general fault-tree language.

Positive fault trees contain only basic events, AND gates, and OR gates.
They exclude NOT, NAND, and NOR gates.
-/
def Positive : GFTree Event → Prop
  | basic _ => True
  | gate GGate.andGate ts =>
      ∀ t ∈ ts, Positive t
  | gate GGate.orGate ts =>
      ∀ t ∈ ts, Positive t
  | gate GGate.notGate _ => False
  | gate GGate.nandGate _ => False
  | gate GGate.norGate _ => False

/-
===========================================================
3. Well-Formedness Simplification Lemmas
===========================================================
-/

/-- Every basic event is well formed. -/
@[simp]
theorem wellFormed_basic
    (e : Event) :
    WellFormed (basic e) := by
  exact WellFormed.basic e

/-- An AND gate is well formed iff it is nonempty and all children are well formed. -/
@[simp]
theorem wellFormed_AND
    (ts : List (GFTree Event)) :
    WellFormed (AND ts) ↔
      ts ≠ [] ∧
      (∀ t ∈ ts, WellFormed t) := by
  unfold AND
  constructor
  · intro h
    cases h with
    | andGate _ hne hall =>
        exact ⟨hne, hall⟩
  · intro h
    rcases h with ⟨hne, hall⟩
    exact WellFormed.andGate ts hne hall

/-- An OR gate is well formed iff it is nonempty and all children are well formed. -/
@[simp]
theorem wellFormed_OR
    (ts : List (GFTree Event)) :
    WellFormed (OR ts) ↔
      ts ≠ [] ∧
      (∀ t ∈ ts, WellFormed t) := by
  unfold OR
  constructor
  · intro h
    cases h with
    | orGate _ hne hall =>
        exact ⟨hne, hall⟩
  · intro h
    rcases h with ⟨hne, hall⟩
    exact WellFormed.orGate ts hne hall

/-- A NOT gate is well formed iff its child is well formed. -/
@[simp]
theorem wellFormed_NOT
    (t : GFTree Event) :
    WellFormed (NOT t) ↔
      WellFormed t := by
  unfold NOT
  constructor
  · intro h
    cases h with
    | notGate _ h =>
        simpa using h
  · intro h
    exact WellFormed.notGate t h

/-- A NAND gate is well formed iff it is nonempty and all children are well formed. -/
@[simp]
theorem wellFormed_NAND
    (ts : List (GFTree Event)) :
    WellFormed (NAND ts) ↔
      ts ≠ [] ∧
      (∀ t ∈ ts, WellFormed t) := by
  unfold NAND
  constructor
  · intro h
    cases h with
    | nandGate _ hne hall =>
        exact ⟨hne, hall⟩
  · intro h
    rcases h with ⟨hne, hall⟩
    exact WellFormed.nandGate ts hne hall

/-- A NOR gate is well formed iff it is nonempty and all children are well formed. -/
@[simp]
theorem wellFormed_NOR
    (ts : List (GFTree Event)) :
    WellFormed (NOR ts) ↔
      ts ≠ [] ∧
      (∀ t ∈ ts, WellFormed t) := by
  unfold NOR
  constructor
  · intro h
    cases h with
    | norGate _ hne hall =>
        exact ⟨hne, hall⟩
  · intro h
    rcases h with ⟨hne, hall⟩
    exact WellFormed.norGate ts hne hall

/-
===========================================================
4. Well-Formedness Inversion Lemmas
===========================================================
-/

/-- Every child of a well-formed AND gate is well formed. -/
theorem wellFormed_child_AND
    {ts : List (GFTree Event)}
    (h : WellFormed (AND ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    WellFormed t := by
  exact ((wellFormed_AND ts).mp h).2 t ht

/-- Every child of a well-formed OR gate is well formed. -/
theorem wellFormed_child_OR
    {ts : List (GFTree Event)}
    (h : WellFormed (OR ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    WellFormed t := by
  exact ((wellFormed_OR ts).mp h).2 t ht

/-- The child of a well-formed NOT gate is well formed. -/
theorem wellFormed_child_NOT
    {t : GFTree Event}
    (h : WellFormed (NOT t)) :
    WellFormed t := by
  exact (wellFormed_NOT t).mp h

/-- Every child of a well-formed NAND gate is well formed. -/
theorem wellFormed_child_NAND
    {ts : List (GFTree Event)}
    (h : WellFormed (NAND ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    WellFormed t := by
  exact ((wellFormed_NAND ts).mp h).2 t ht

/-- Every child of a well-formed NOR gate is well formed. -/
theorem wellFormed_child_NOR
    {ts : List (GFTree Event)}
    (h : WellFormed (NOR ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    WellFormed t := by
  exact ((wellFormed_NOR ts).mp h).2 t ht

/-- A well-formed AND gate has at least one child. -/
theorem wellFormed_AND_nonempty
    {ts : List (GFTree Event)}
    (h : WellFormed (AND ts)) :
    ts ≠ [] := by
  exact ((wellFormed_AND ts).mp h).1

/-- A well-formed OR gate has at least one child. -/
theorem wellFormed_OR_nonempty
    {ts : List (GFTree Event)}
    (h : WellFormed (OR ts)) :
    ts ≠ [] := by
  exact ((wellFormed_OR ts).mp h).1

/-- A well-formed NAND gate has at least one child. -/
theorem wellFormed_NAND_nonempty
    {ts : List (GFTree Event)}
    (h : WellFormed (NAND ts)) :
    ts ≠ [] := by
  exact ((wellFormed_NAND ts).mp h).1

/-- A well-formed NOR gate has at least one child. -/
theorem wellFormed_NOR_nonempty
    {ts : List (GFTree Event)}
    (h : WellFormed (NOR ts)) :
    ts ≠ [] := by
  exact ((wellFormed_NOR ts).mp h).1

/-
===========================================================
5. Positive Simplification Lemmas
===========================================================
-/

/-- Basic events are positive. -/
@[simp]
theorem positive_basic
    (e : Event) :
    Positive (basic e) := by
  simp [Positive]

/-- An AND gate is positive iff all of its children are positive. -/
@[simp]
theorem positive_AND
    (ts : List (GFTree Event)) :
    Positive (AND ts) ↔
      ∀ t ∈ ts, Positive t := by
  simp [AND, Positive]

/-- An OR gate is positive iff all of its children are positive. -/
@[simp]
theorem positive_OR
    (ts : List (GFTree Event)) :
    Positive (OR ts) ↔
      ∀ t ∈ ts, Positive t := by
  simp [OR, Positive]

/-- A NOT gate is never positive. -/
@[simp]
theorem positive_NOT_iff
    (t : GFTree Event) :
    Positive (NOT t) ↔ False := by
  simp [NOT, Positive]

/-- A NAND gate is never positive. -/
@[simp]
theorem positive_NAND_iff
    (ts : List (GFTree Event)) :
    Positive (NAND ts) ↔ False := by
  simp [NAND, Positive]

/-- A NOR gate is never positive. -/
@[simp]
theorem positive_NOR_iff
    (ts : List (GFTree Event)) :
    Positive (NOR ts) ↔ False := by
  simp [NOR, Positive]

/-- A NOT gate is not positive. -/
theorem not_positive_NOT
    (t : GFTree Event) :
    ¬ Positive (NOT t) := by
  simp

/-- A NAND gate is not positive. -/
theorem not_positive_NAND
    (ts : List (GFTree Event)) :
    ¬ Positive (NAND ts) := by
  simp

/-- A NOR gate is not positive. -/
theorem not_positive_NOR
    (ts : List (GFTree Event)) :
    ¬ Positive (NOR ts) := by
  simp

/-
===========================================================
6. Positive Inversion Lemmas
===========================================================
-/

/-- Every child of a positive AND gate is positive. -/
theorem positive_child_AND
    {ts : List (GFTree Event)}
    (h : Positive (AND ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    Positive t := by
  exact ((positive_AND ts).mp h) t ht

/-- Every child of a positive OR gate is positive. -/
theorem positive_child_OR
    {ts : List (GFTree Event)}
    (h : Positive (OR ts))
    {t : GFTree Event}
    (ht : t ∈ ts) :
    Positive t := by
  exact ((positive_OR ts).mp h) t ht

/-- A positive gate can only be an AND gate or an OR gate. -/
theorem positive_gate
    {g : GGate}
    {ts : List (GFTree Event)}
    (h : Positive (gate g ts)) :
    g = GGate.andGate ∨ g = GGate.orGate := by
  cases g <;> simp [Positive] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
Every positive tree contains only AND and OR gates at its root.
-/
theorem positive_gate_characterization
    (t : GFTree Event)
    (h : Positive t) :
    ¬ gateOf t = some GGate.notGate ∧
    ¬ gateOf t = some GGate.nandGate ∧
    ¬ gateOf t = some GGate.norGate := by
  cases t with
  | basic e =>
      simp [gateOf]
  | gate g ts =>
      cases g <;> simp [Positive, gateOf] at h ⊢

end GFTree
