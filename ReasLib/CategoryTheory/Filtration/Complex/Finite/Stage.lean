/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient

/-!
# Filtration Stages of Bounded-Below Finite Filtered Complexes

This leaf restricts stage evaluation to finite filtered objects and lifts it canonically to
bounded-below cochain complexes and their homotopy category.  Each layer is obtained by composing
existing functors, so the construction introduces neither new functor laws nor choices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.Stage

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C]
  [Preadditive C] [HasZeroObject C]

/-- Evaluate the `p`-th filtration stage of a finite filtered object. -/
@[stacks 05RZ "finite filtered stage functor"]
noncomputable abbrev functor (p : ℤ) :
    FilteredObject.Finite.category C ⥤ C :=
  FilteredObject.Finite.inclusion C ⋙ FilteredObject.Stage.functor p

namespace functor

/-- Objectwise computation for the finite filtered stage functor. -/
@[simp, stacks 05RZ "finite filtered stage computation"]
theorem obj (p : ℤ) (X : FilteredObject.Finite.category C) :
    (functor C p).obj X = X.obj.stage p := sorry

/-- Morphismwise computation for the finite filtered stage functor. -/
@[simp, stacks 05RZ "finite filtered stage computation"]
theorem map (p : ℤ) {X Y : FilteredObject.Finite.category C} (f : X ⟶ Y) :
    (functor C p).map f =
      ((FilteredObject.Finite.inclusion C).map f).stageMap p := sorry

end functor

/-- Evaluate the `p`-th filtration stage degreewise on bounded-below complexes of finite
filtered objects. -/
@[stacks 05RZ "bounded-below finite filtered stage cochain functor"]
noncomputable abbrev cochain (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ CochainComplex.Plus C :=
  (functor C p).mapCochainComplexPlus

namespace cochain

/-- Objectwise computation for the bounded-below finite filtered stage cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered stage cochain computation"]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (cochain C p).obj K = (functor C p).mapCochainComplexPlus.obj K := sorry

/-- Morphismwise computation for the bounded-below finite filtered stage cochain functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered stage cochain computation"]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (cochain C p).map f = (functor C p).mapCochainComplexPlus.map f := sorry

end cochain

/-- Evaluate the `p`-th stage of a bounded-below finite filtered complex and pass to the
bounded-below homotopy category. -/
@[stacks 05RZ "bounded-below finite filtered stage homotopy functor"]
noncomputable abbrev homotopy (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ HomotopyCategory.Plus C :=
  cochain C p ⋙ HomotopyCategory.Plus.quotient C

namespace homotopy

/-- Objectwise computation for the bounded-below finite filtered stage homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered stage homotopy computation"]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (homotopy C p).obj K =
      (HomotopyCategory.Plus.quotient C).obj ((cochain C p).obj K) := sorry

/-- Morphismwise computation for the bounded-below finite filtered stage homotopy functor. -/
@[simp, stacks 05RZ "bounded-below finite filtered stage homotopy computation"]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (homotopy C p).map f =
      (HomotopyCategory.Plus.quotient C).map ((cochain C p).map f) := sorry

end homotopy

end CategoryTheory.FilteredObject.Finite.Stage
