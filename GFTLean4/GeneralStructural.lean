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
set_option linter.flexible false

/-!
  Structural analysis of general fault trees.

  This file defines reusable structural functions and predicates:
  size, height, event counts, gate counts, degree, event sets,
  subtree relation, and event occurrence.
-/

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Structural Measures
===========================================================
-/

/-- Total number of nodes in a general fault tree. -/
def size : GFTree Event → Nat
  | basic _ => 1
  | gate _ ts => 1 + (ts.map size).sum

/-- Height of a general fault tree. -/
def height : GFTree Event → Nat
  | basic _ => 1
  | gate _ ts => 1 + (ts.map height).foldl Nat.max 0

/-- Number of basic-event leaves in a general fault tree. -/
def basicEventCount : GFTree Event → Nat
  | basic _ => 1
  | gate _ ts => (ts.map basicEventCount).sum

/-- Number of gate nodes in a general fault tree. -/
def gateCount : GFTree Event → Nat
  | basic _ => 0
  | gate _ ts => 1 + (ts.map gateCount).sum

/-- Number of immediate children of a general fault tree. -/
def degree : GFTree Event → Nat
  | basic _ => 0
  | gate _ ts => ts.length

/-- Number of leaves in a general fault tree. -/
def leafCount : GFTree Event → Nat
  | basic _ => 1
  | gate _ ts => (ts.map leafCount).sum

/-
===========================================================
2. Event Set
===========================================================
-/

/-- Finite set of basic events appearing in a general fault tree. -/
def events [DecidableEq Event] : GFTree Event → Finset Event
  | basic e => {e}
  | gate _ ts => (ts.map events).foldl (fun acc s => acc ∪ s) ∅

/-
===========================================================
3. Basic Simplification Lemmas
===========================================================
-/

@[simp]
theorem size_basic (e : Event) :
    size (basic e) = 1 := by
  simp [size]

@[simp]
theorem size_gate (g : GGate) (ts : List (GFTree Event)) :
    size (gate g ts) = 1 + (ts.map size).sum := by
  simp [size]

@[simp]
theorem height_basic (e : Event) :
    height (basic e) = 1 := by
  simp [height]

@[simp]
theorem height_gate (g : GGate) (ts : List (GFTree Event)) :
    height (gate g ts) =
      1 + (ts.map height).foldl Nat.max 0 := by
  simp [height]

@[simp]
theorem basicEventCount_basic (e : Event) :
    basicEventCount (basic e) = 1 := by
  simp [basicEventCount]

@[simp]
theorem basicEventCount_gate (g : GGate) (ts : List (GFTree Event)) :
    basicEventCount (gate g ts) =
      (ts.map basicEventCount).sum := by
  simp [basicEventCount]

@[simp]
theorem gateCount_basic (e : Event) :
    gateCount (basic e) = 0 := by
  simp [gateCount]

@[simp]
theorem gateCount_gate (g : GGate) (ts : List (GFTree Event)) :
    gateCount (gate g ts) =
      1 + (ts.map gateCount).sum := by
  simp [gateCount]

@[simp]
theorem degree_basic (e : Event) :
    degree (basic e) = 0 := by
  simp [degree]

@[simp]
theorem degree_gate (g : GGate) (ts : List (GFTree Event)) :
    degree (gate g ts) = ts.length := by
  simp [degree]

@[simp]
theorem leafCount_basic (e : Event) :
    leafCount (basic e) = 1 := by
  simp [leafCount]

@[simp]
theorem leafCount_gate (g : GGate) (ts : List (GFTree Event)) :
    leafCount (gate g ts) =
      (ts.map leafCount).sum := by
  simp [leafCount]

@[simp]
theorem events_basic [DecidableEq Event] (e : Event) :
    events (basic e) = ({e} : Finset Event) := by
  simp [events]

@[simp]
theorem events_gate [DecidableEq Event]
    (g : GGate) (ts : List (GFTree Event)) :
    events (gate g ts) =
      (ts.map events).foldl (fun acc s => acc ∪ s) ∅ := by
  simp [events]

/-
===========================================================
4. Structural Positivity Lemmas
===========================================================
-/

/-- Every general fault tree has positive size. -/
theorem size_pos (t : GFTree Event) :
    0 < size t := by
  cases t <;> simp

/-- Every general fault tree has positive height. -/
theorem height_pos (t : GFTree Event) :
    0 < height t := by
  cases t <;> simp

/-- A gate node always has positive size. -/
theorem size_gate_pos (g : GGate) (ts : List (GFTree Event)) :
    0 < size (gate g ts) := by
  simp

/-- A gate node always has positive height. -/
theorem height_gate_pos (g : GGate) (ts : List (GFTree Event)) :
    0 < height (gate g ts) := by
  simp

/-
===========================================================
5. Subtree Relation
===========================================================
-/

/--
`Subtree s t` means that `s` is a subtree of `t`.

The relation is reflexive and closed under child membership.
-/
inductive Subtree : GFTree Event → GFTree Event → Prop where
  | refl (t : GFTree Event) :
      Subtree t t
  | child {g : GGate} {ts : List (GFTree Event)}
      {s t : GFTree Event} :
      t ∈ ts →
      Subtree s t →
      Subtree s (gate g ts)

/-- Every tree is a subtree of itself. -/
theorem subtree_refl (t : GFTree Event) :
    Subtree t t := by
  exact Subtree.refl t

/-- A subtree of a child is a subtree of the parent gate. -/
theorem subtree_gate_of_child
    (g : GGate) (ts : List (GFTree Event))
    {s t : GFTree Event}
    (hMem : t ∈ ts)
    (hSub : Subtree s t) :
    Subtree s (gate g ts) := by
  exact Subtree.child hMem hSub

/-
===========================================================
6. Event Occurrence
===========================================================
-/

/--
`Occurs e t` means that basic event `e` occurs somewhere in
the general fault tree `t`.
-/
inductive Occurs (e : Event) : GFTree Event → Prop where
  | basic :
      Occurs e (basic e)
  | child {g : GGate} {ts : List (GFTree Event)} {t : GFTree Event} :
      Occurs e t →
      t ∈ ts →
      Occurs e (gate g ts)

/-- Every event occurs in its own basic-event node. -/
theorem occurs_basic_self (e : Event) :
    Occurs e (basic e) := by
  exact Occurs.basic

/-- Occurrence in a basic-event node is equivalent to equality. -/
@[simp]
theorem occurs_basic_iff (e x : Event) :
    Occurs e (basic x) ↔ e = x := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Occurs.basic

/-- If an event occurs in a child, then it occurs in the parent gate. -/
theorem occurs_gate_of_child
    (e : Event) (g : GGate) (ts : List (GFTree Event))
    (t : GFTree Event)
    (hOccurs : Occurs e t)
    (hMem : t ∈ ts) :
    Occurs e (gate g ts) := by
  exact Occurs.child hOccurs hMem

/-- Occurrence in a gate is equivalent to occurrence in one of its children. -/
theorem occurs_gate_iff
    (e : Event) (g : GGate) (ts : List (GFTree Event)) :
    Occurs e (gate g ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  constructor
  · intro h
    cases h with
    | child hOcc hMem =>
        exact ⟨_, hMem, hOcc⟩
  · intro h
    rcases h with ⟨t, hMem, hOcc⟩
    exact Occurs.child hOcc hMem

/-- Occurrence in an AND smart constructor comes from one of its children. -/
theorem occurs_AND_iff
    (e : Event) (ts : List (GFTree Event)) :
    Occurs e (AND ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  unfold AND
  exact occurs_gate_iff e GGate.andGate ts

/-- Occurrence in an OR smart constructor comes from one of its children. -/
theorem occurs_OR_iff
    (e : Event) (ts : List (GFTree Event)) :
    Occurs e (OR ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  unfold OR
  exact occurs_gate_iff e GGate.orGate ts

/-- Occurrence in a NOT smart constructor is occurrence in its child. -/
theorem occurs_NOT_iff
    (e : Event) (t : GFTree Event) :
    Occurs e (NOT t) ↔ Occurs e t := by
  unfold NOT
  rw [occurs_gate_iff]
  constructor
  · intro h
    rcases h with ⟨s, hs, hOcc⟩
    simp at hs
    subst hs
    exact hOcc
  · intro h
    exact ⟨t, by simp, h⟩

/-- Occurrence in a NAND smart constructor comes from one of its children. -/
theorem occurs_NAND_iff
    (e : Event) (ts : List (GFTree Event)) :
    Occurs e (NAND ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  unfold NAND
  exact occurs_gate_iff e GGate.nandGate ts

/-- Occurrence in a NOR smart constructor comes from one of its children. -/
theorem occurs_NOR_iff
    (e : Event) (ts : List (GFTree Event)) :
    Occurs e (NOR ts) ↔
      ∃ t ∈ ts, Occurs e t := by
  unfold NOR
  exact occurs_gate_iff e GGate.norGate ts

/-- Every child of a gate has smaller size than the gate itself. -/
theorem size_lt_gate_of_mem
    (g : GGate) (ts : List (GFTree Event)) {t : GFTree Event}
    (hMem : t ∈ ts) :
    size t < size (gate g ts) := by
  simp
  have hIn : size t ∈ ts.map size := by
    exact List.mem_map.mpr ⟨t, hMem, rfl⟩
  have hLe : size t ≤ (ts.map size).sum := by
    exact List.le_sum_of_mem hIn
  omega

end GFTree
