/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import Mathlib

set_option linter.style.header false

/-
  Syntax of general fault trees.

  This file defines only the core language of general fault trees:
  gate symbols, tree constructors, smart constructors, and basic
  syntactic views.
-/

/-!
`GGate` represents the gate types supported by general fault trees.

* `andGate`  means all children must occur.
* `orGate`   means at least one child must occur.
* `notGate`  means the single child must not occur.
* `nandGate` means not all children occur.
* `norGate`  means no child occurs.
-/
inductive GGate where
  | andGate  : GGate
  | orGate   : GGate
  | notGate  : GGate
  | nandGate : GGate
  | norGate  : GGate
deriving Repr, DecidableEq

/--
`GFTree Event` is the type of general fault trees whose basic events
have type `Event`.

A general fault tree is either:

* `basic e`, representing a basic event `e`;
* `gate g ts`, representing a gate `g` applied to child trees.
-/
inductive GFTree (Event : Type) where
  | basic : Event → GFTree Event
  | gate  : GGate → List (GFTree Event) → GFTree Event
deriving Repr

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Smart Constructors
===========================================================
-/

/-- Construct a basic event node. -/
def BE (e : Event) : GFTree Event :=
  basic e

/-- Construct an AND gate. -/
def AND (ts : List (GFTree Event)) : GFTree Event :=
  gate GGate.andGate ts

/-- Construct an OR gate. -/
def OR (ts : List (GFTree Event)) : GFTree Event :=
  gate GGate.orGate ts

/-- Construct a NOT gate. -/
def NOT (t : GFTree Event) : GFTree Event :=
  gate GGate.notGate [t]

/-- Construct a NAND gate. -/
def NAND (ts : List (GFTree Event)) : GFTree Event :=
  gate GGate.nandGate ts

/-- Construct a NOR gate. -/
def NOR (ts : List (GFTree Event)) : GFTree Event :=
  gate GGate.norGate ts

/-
===========================================================
2. Basic Views
===========================================================
-/

/-- `isBasic t` holds exactly when `t` is a basic event node. -/
def isBasic : GFTree Event → Prop
  | basic _ => True
  | gate _ _ => False

/-- `isGate t` holds exactly when `t` is a gate node. -/
def isGate : GFTree Event → Prop
  | basic _ => False
  | gate _ _ => True

/-- Return the immediate children of a general fault tree. -/
def children : GFTree Event → List (GFTree Event)
  | basic _ => []
  | gate _ ts => ts

/-- Return the gate label of a general fault tree, if one exists. -/
def gateOf : GFTree Event → Option GGate
  | basic _ => none
  | gate g _ => some g

/-
===========================================================
3. Syntax Simplification Lemmas
===========================================================
-/

/-- A basic event has no children. -/
@[simp]
theorem children_basic (e : Event) :
    children (basic e) = [] := by
  simp [children]

/-- The children of a gate are exactly its child list. -/
@[simp]
theorem children_gate (g : GGate) (ts : List (GFTree Event)) :
    children (gate g ts) = ts := by
  simp [children]

/-- A basic event has no root gate. -/
@[simp]
theorem gateOf_basic (e : Event) :
    gateOf (basic e) = none := by
  simp [gateOf]

/-- The root gate of a gate node is its gate label. -/
@[simp]
theorem gateOf_gate (g : GGate) (ts : List (GFTree Event)) :
    gateOf (gate g ts) = some g := by
  simp [gateOf]

/-- A basic event is syntactically basic. -/
@[simp]
theorem isBasic_basic (e : Event) :
    isBasic (basic e) := by
  simp [isBasic]

/-- A gate node is not syntactically basic. -/
@[simp]
theorem not_isBasic_gate (g : GGate) (ts : List (GFTree Event)) :
    ¬ isBasic (gate g ts) := by
  simp [isBasic]

/-- A basic event is not a gate node. -/
@[simp]
theorem not_isGate_basic (e : Event) :
    ¬ isGate (basic e) := by
  simp [isGate]

/-- A gate node is syntactically a gate. -/
@[simp]
theorem isGate_gate (g : GGate) (ts : List (GFTree Event)) :
    isGate (gate g ts) := by
  simp [isGate]

end GFTree
