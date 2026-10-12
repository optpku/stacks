/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Supremum
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Interval

@[expose] public section

/-!
# Suprema of Extension Constructions

This leaf records when extension products commute with a supremum. Generic
colimit, finite-coproduct, and retract-closure formulas are owned by
`ReasLib.CategoryTheory.ObjectProperty.Supremum`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {ι : Sort*}

/-- Taking a bounded shift interval commutes with an arbitrary supremum. -/
@[stacks 0FX6]
theorem shiftInterval_iSup (P : ι → ObjectProperty C) (a b : ℤ) :
    (⨆ i, P i)[a, b] = ⨆ i, (P i)[a, b] := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Sort*}

/-- Extension product commutes with a supremum in its left argument. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_left (P : ι → ObjectProperty C) (Q : ObjectProperty C) :
    extensionProduct (⨆ i, P i) Q = ⨆ i, extensionProduct (P i) Q := sorry

/-- Extension product commutes with a supremum in its right argument. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_right (P : ObjectProperty C) (Q : ι → ObjectProperty C) :
    extensionProduct P (⨆ i, Q i) = ⨆ i, extensionProduct P (Q i) := sorry

/-- Extension product commutes with the diagonal supremum of two directed nonempty families. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_of_directed
    {κ : Type*} [Nonempty κ] (P Q : κ → ObjectProperty C)
    (hP : Directed (· ≤ ·) P) (hQ : Directed (· ≤ ·) Q) :
    extensionProduct (⨆ i, P i) (⨆ i, Q i) = ⨆ i, extensionProduct (P i) (Q i) := sorry

/-- Extension product commutes with the diagonal supremum of two monotone sequences. -/
@[stacks 0FX6]
theorem extensionProduct_iSup_of_monotone
    (P Q : ℕ → ObjectProperty C) (hP : Monotone P) (hQ : Monotone Q) :
    extensionProduct (⨆ n, P n) (⨆ n, Q n) = ⨆ n, extensionProduct (P n) (Q n) := sorry

/-- Iterated extension product commutes with the supremum of a monotone sequence. -/
@[stacks 0FX6]
theorem extensionProductIter_iSup_of_monotone (P : ℕ → ObjectProperty C) (hP : Monotone P)
    (n : ℕ) :
    (⨆ i, P i).extensionProductIter n = ⨆ i, (P i).extensionProductIter n := sorry

/-- Iterated extension product commutes with the supremum of a directed nonempty family. -/
@[stacks 0FX6]
theorem extensionProductIter_iSup_of_directed
    {κ : Type*} [Nonempty κ] (P : κ → ObjectProperty C)
    (hP : Directed (· ≤ ·) P) (n : ℕ) :
    (⨆ i, P i).extensionProductIter n = ⨆ i, (P i).extensionProductIter n := sorry

end

end CategoryTheory.ObjectProperty
