/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralBooleanAlgebra
import GFTLean4.GeneralStructural

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false
set_option linter.flexible false

/-
  Monotonicity theory for general fault trees.

  This file proves that the positive fragment of the general
  fault-tree language is monotone with respect to enlarging
  the active cut set.
-/

namespace GFTree

variable {Event : Type}

/-
===========================================================
1. Cut-set Inclusion
===========================================================
-/

/-- `CutSubset C₁ C₂` means every event active in `C₁` is also active in `C₂`. -/
def CutSubset
    (C₁ C₂ : CutSet Event) : Prop :=
  ∀ e, e ∈ C₁ → e ∈ C₂

/-- Cut-set inclusion is reflexive. -/
@[refl]
theorem CutSubset.refl
    (C : CutSet Event) :
    CutSubset C C := by
  intro e h
  exact h

/-- Cut-set inclusion is transitive. -/
@[trans]
theorem CutSubset.trans
    {A B C : CutSet Event}
    (h₁ : CutSubset A B)
    (h₂ : CutSubset B C) :
    CutSubset A C := by
  intro e h
  exact h₂ e (h₁ e h)

/-
===========================================================
2. Monotone Predicate
===========================================================
-/

/--
A fault tree is monotone if enlarging the active cut set
cannot change a true evaluation into false.
-/
def Monotone [DecidableEq Event]
    (t : GFTree Event) : Prop :=
  ∀ C₁ C₂ : CutSet Event,
    CutSubset C₁ C₂ →
    eval C₁ t = true →
    eval C₂ t = true

/-
===========================================================
3. Basic Events
===========================================================
-/

/-- Basic-event trees are monotone. -/
theorem monotone_basic [DecidableEq Event]
    (e : Event) :
    Monotone (basic e) := by
  intro C₁ C₂ hSub hEval
  simp [eval] at hEval ⊢
  exact hSub e hEval

/-
===========================================================
4. Monotonicity of AND and OR Lists
===========================================================
-/

/--
If every tree in a list is monotone, then `evalAll` is monotone
with respect to cut-set inclusion.
-/
theorem evalAll_monotone
    [DecidableEq Event]
    (C₁ C₂ : CutSet Event)
    (hSub : CutSubset C₁ C₂)
    (ts : List (GFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t)
    (hEval : evalAll C₁ ts = true) :
    evalAll C₂ ts = true := by
  induction ts with
  | nil =>
      simp [evalAll]
  | cons t ts ih =>
      simp [evalAll] at hEval ⊢
      rcases hEval with ⟨ht, hts⟩

      have hMonoHead : Monotone t := by
        exact hMono t (by simp)

      have hMonoTail :
          ∀ s ∈ ts, Monotone s := by
        intro s hs
        exact hMono s (by simp [hs])

      have ht' : eval C₂ t = true := by
        exact hMonoHead C₁ C₂ hSub ht

      have hts' : evalAll C₂ ts = true := by
        exact ih hMonoTail hts

      simp [ht', hts']

/--
If every tree in a list is monotone, then `evalAny` is monotone
with respect to cut-set inclusion.
-/
theorem evalAny_monotone
    [DecidableEq Event]
    (C₁ C₂ : CutSet Event)
    (hSub : CutSubset C₁ C₂)
    (ts : List (GFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t)
    (hEval : evalAny C₁ ts = true) :
    evalAny C₂ ts = true := by
  induction ts with
  | nil =>
      simp [evalAny] at hEval
  | cons t ts ih =>
      simp [evalAny] at hEval ⊢

      cases hCt : eval C₁ t with
      | false =>
          have hTail : evalAny C₁ ts = true := by
            simpa [hCt] using hEval

          have hMonoTail :
              ∀ s ∈ ts, Monotone s := by
            intro s hs
            exact hMono s (by simp [hs])

          right
          exact ih hMonoTail hTail

      | true =>
          have hMonoHead : Monotone t := by
            exact hMono t (by simp)

          have hDt : eval C₂ t = true := by
            exact hMonoHead C₁ C₂ hSub hCt

          left
          exact hDt

/-
===========================================================
5. Monotonicity of Positive Gates
===========================================================
-/

/-- An AND gate is monotone if all of its children are monotone. -/
theorem monotone_AND
    [DecidableEq Event]
    (ts : List (GFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t) :
    Monotone (AND ts) := by
  intro C₁ C₂ hSub hEval

  have hAll₁ : evalAll C₁ ts = true := by
    simpa [eval_AND] using hEval

  have hAll₂ : evalAll C₂ ts = true := by
    exact evalAll_monotone C₁ C₂ hSub ts hMono hAll₁

  simpa [eval_AND] using hAll₂

/-- An OR gate is monotone if all of its children are monotone. -/
theorem monotone_OR
    [DecidableEq Event]
    (ts : List (GFTree Event))
    (hMono : ∀ t ∈ ts, Monotone t) :
    Monotone (OR ts) := by
  intro C₁ C₂ hSub hEval

  have hAny₁ : evalAny C₁ ts = true := by
    simpa [eval_OR] using hEval

  have hAny₂ : evalAny C₂ ts = true := by
    exact evalAny_monotone C₁ C₂ hSub ts hMono hAny₁

  simpa [eval_OR] using hAny₂

/-
===========================================================
6. Main Monotonicity Theorem
===========================================================
-/

/--
Every positive general fault tree is monotone.
-/
theorem positive_monotone
    [DecidableEq Event] :
    ∀ t : GFTree Event, Positive t → Monotone t
  | basic e, _ => by
      exact monotone_basic e

  | gate GGate.andGate ts, hPos => by
      apply monotone_AND
      intro t ht
      have hChildren :
          ∀ s ∈ ts, Positive s := by
        simpa [Positive] using hPos
      exact positive_monotone t (hChildren t ht)

  | gate GGate.orGate ts, hPos => by
      apply monotone_OR
      intro t ht
      have hChildren :
          ∀ s ∈ ts, Positive s := by
        simpa [Positive] using hPos
      exact positive_monotone t (hChildren t ht)

  | gate GGate.notGate ts, hPos => by
      simp [Positive] at hPos

  | gate GGate.nandGate ts, hPos => by
      simp [Positive] at hPos

  | gate GGate.norGate ts, hPos => by
      simp [Positive] at hPos
termination_by t _ => size t
decreasing_by
  all_goals
    exact size_lt_gate_of_mem _ _ ‹_ ∈ _›

/-- The positive fragment of the general fault-tree language is monotone. -/
theorem positive_fragment_monotone
    [DecidableEq Event]
    {t : GFTree Event}
    (h : Positive t) :
    Monotone t := by
  exact positive_monotone t h

/-
===========================================================
7. Non-Monotonicity of General Fault Trees
===========================================================
-/

/--
A single NOT gate over a basic event is not monotone.

This shows that general fault trees are not monotone in general.
-/
theorem not_basic_not_monotone
    [DecidableEq Event]
    (e : Event) :
    ¬ Monotone (NOT (basic e)) := by
  intro hMono

  let C₁ : CutSet Event := ∅
  let C₂ : CutSet Event := {e}

  have hSub : CutSubset C₁ C₂ := by
    intro x hx
    simp [C₁] at hx

  have hEval₁ : eval C₁ (NOT (basic e)) = true := by
    simp [C₁, NOT, eval]

  have hEval₂ : eval C₂ (NOT (basic e)) = true := by
    exact hMono C₁ C₂ hSub hEval₁

  simp [C₂, NOT, eval] at hEval₂

/--
A single NAND gate over a basic event is not monotone.
-/
theorem nand_basic_not_monotone
    [DecidableEq Event]
    (e : Event) :
    ¬ Monotone (NAND [basic e]) := by
  intro hMono

  let C₁ : CutSet Event := ∅
  let C₂ : CutSet Event := {e}

  have hSub : CutSubset C₁ C₂ := by
    intro x hx
    simp [C₁] at hx

  have hEval₁ : eval C₁ (NAND [basic e]) = true := by
    simp [C₁, NAND, evalAll, eval]

  have hEval₂ : eval C₂ (NAND [basic e]) = true := by
    exact hMono C₁ C₂ hSub hEval₁

  simp [C₂, NAND, evalAll, eval] at hEval₂

/--
A single NOR gate over a basic event is not monotone.
-/
theorem nor_basic_not_monotone
    [DecidableEq Event]
    (e : Event) :
    ¬ Monotone (NOR [basic e]) := by
  intro hMono

  let C₁ : CutSet Event := ∅
  let C₂ : CutSet Event := {e}

  have hSub : CutSubset C₁ C₂ := by
    intro x hx
    simp [C₁] at hx

  have hEval₁ : eval C₁ (NOR [basic e]) = true := by
    simp [C₁, NOR, evalAny, eval]

  have hEval₂ : eval C₂ (NOR [basic e]) = true := by
    exact hMono C₁ C₂ hSub hEval₁

  simp [C₂, NOR, evalAny, eval] at hEval₂

end GFTree
