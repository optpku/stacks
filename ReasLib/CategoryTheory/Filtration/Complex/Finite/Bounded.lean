/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Functors on Finite Filtered Complexes

This leaf restricts the graded-piece and forgetful functors to bounded-below cochain complexes
and packages their composites with the bounded-below homotopy quotient.  It is independent of
derived functors and spectral sequences, so those applications can share the same source-level
owners and computation API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.Plus

namespace GradedPiece

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C]
  [Preadditive C] [HasZeroObject C] [HasCokernels C]

/-- Take the `p`-th associated-graded piece degreewise on bounded-below cochain complexes of
finite filtered objects. -/
@[stacks 05RZ "bounded-below finite filtered graded-piece cochain functor"]
noncomputable abbrev cochain (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ CochainComplex.Plus C :=
  (FilteredObject.Finite.AssociatedGraded.functor C ⋙
    GradedObject.eval p).mapCochainComplexPlus

namespace cochain

/-- Objectwise computation for the bounded-below graded-piece cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered graded-piece cochain computation"]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (cochain C p).obj K =
      ((FilteredObject.Finite.AssociatedGraded.functor C ⋙
        GradedObject.eval p).mapCochainComplexPlus).obj K := sorry

/-- Morphismwise computation for the bounded-below graded-piece cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered graded-piece cochain computation"]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (cochain C p).map f =
      ((FilteredObject.Finite.AssociatedGraded.functor C ⋙
        GradedObject.eval p).mapCochainComplexPlus).map f := sorry

end cochain

/-- Take the `p`-th associated-graded piece of a bounded-below finite filtered complex and pass
it to the bounded-below homotopy category. -/
@[stacks 05RZ "bounded-below finite filtered graded-piece homotopy functor"]
noncomputable abbrev homotopy (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ HomotopyCategory.Plus C :=
  cochain C p ⋙ HomotopyCategory.Plus.quotient C

namespace homotopy

/-- Objectwise computation for the bounded-below graded-piece homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered graded-piece homotopy computation"]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (homotopy C p).obj K =
      (HomotopyCategory.Plus.quotient C).obj ((cochain C p).obj K) := sorry

/-- Morphismwise computation for the bounded-below graded-piece homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered graded-piece homotopy computation"]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (homotopy C p).map f =
      (HomotopyCategory.Plus.quotient C).map ((cochain C p).map f) := sorry

end homotopy

end GradedPiece

namespace Forget

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C]
  [Preadditive C] [HasZeroObject C]

/-- Forget finite filtrations degreewise on bounded-below cochain complexes. -/
@[stacks 05RZ "bounded-below finite filtered forgetful cochain functor"]
noncomputable abbrev cochain :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ CochainComplex.Plus C :=
  (FilteredObject.Finite.Forget.functor C).mapCochainComplexPlus

namespace cochain

/-- Objectwise computation for the bounded-below finite filtered forgetful cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered forgetful cochain computation"]
theorem obj (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (cochain C).obj K =
      ((FilteredObject.Finite.Forget.functor C).mapCochainComplexPlus).obj K := sorry

/-- Morphismwise computation for the bounded-below finite filtered forgetful cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered forgetful cochain computation"]
theorem map {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (cochain C).map f =
      ((FilteredObject.Finite.Forget.functor C).mapCochainComplexPlus).map f := sorry

end cochain

/-- Forget finite filtrations on bounded-below cochain complexes and pass to the bounded-below
homotopy category. -/
@[stacks 05RZ "bounded-below finite filtered forgetful homotopy functor"]
noncomputable abbrev homotopy :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ HomotopyCategory.Plus C :=
  cochain C ⋙ HomotopyCategory.Plus.quotient C

namespace homotopy

/-- Objectwise computation for the bounded-below finite filtered forgetful homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered forgetful homotopy computation"]
theorem obj (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (homotopy C).obj K =
      (HomotopyCategory.Plus.quotient C).obj ((cochain C).obj K) := sorry

/-- Morphismwise computation for the bounded-below finite filtered forgetful homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered forgetful homotopy computation"]
theorem map {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (homotopy C).map f =
      (HomotopyCategory.Plus.quotient C).map ((cochain C).map f) := sorry

end homotopy

end Forget

end CategoryTheory.FilteredObject.Finite.Plus
