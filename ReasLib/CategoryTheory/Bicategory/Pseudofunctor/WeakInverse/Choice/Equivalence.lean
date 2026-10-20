module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Comparison.Left
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Comparison.Right

/-!
# Weak-inverse data for a chosen pseudoinverse

This file packages the source- and target-side comparison equivalences as a
weak inverse and records that the chosen pseudoinverse is a biequivalence.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open scoped Bicategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

/-- The chosen pseudoinverse and its two comparison equivalences. -/
noncomputable def chosenWeakInverse (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    WeakInverse F F.chosenInverse where
  left := ChosenInverse.leftEquivalence F
  right := ChosenInverse.rightEquivalence F

/-- The chosen pseudoinverse of a biequivalence is itself a biequivalence. -/
instance chosenInverse.isBiequivalence (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    F.chosenInverse.IsBiequivalence := sorry

end CategoryTheory.Pseudofunctor
