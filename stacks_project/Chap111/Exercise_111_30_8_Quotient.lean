module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient

/-!
# Filtration quotients of bounded-below finite filtered complexes

This leaf restricts quotient-by-`F^p` evaluation to finite filtered objects and lifts it
canonically to bounded-below cochain complexes.  Each layer is obtained by composing existing
functors, so the construction introduces neither new functor laws nor choices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.Quotient

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C]
  [Preadditive C] [HasZeroObject C] [HasCokernels C]

/-- Evaluate the `p`-th filtration quotient of a finite filtered object. -/
noncomputable abbrev functor (p : ℤ) :
    FilteredObject.Finite.category C ⥤ C :=
  FilteredObject.Finite.inclusion C ⋙ FilteredObject.quotientFunctor p

namespace functor

/-- Objectwise computation for the finite filtered quotient functor. -/
@[simp]
theorem obj (p : ℤ) (X : FilteredObject.Finite.category C) :
    (functor C p).obj X = X.obj.quotient p := sorry

/-- Morphismwise computation for the finite filtered quotient functor. -/
@[simp]
theorem map (p : ℤ) {X Y : FilteredObject.Finite.category C} (f : X ⟶ Y) :
    (functor C p).map f =
      ((FilteredObject.Finite.inclusion C).map f).quotientMap p := sorry

end functor

/-- Evaluate the `p`-th filtration quotient degreewise on bounded-below complexes of finite
filtered objects. -/
noncomputable abbrev cochain (p : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category C) ⥤ CochainComplex.Plus C :=
  (functor C p).mapCochainComplexPlus

namespace cochain

/-- Objectwise computation for the bounded-below finite filtered quotient cochain functor. -/
@[simp]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (cochain C p).obj K = (functor C p).mapCochainComplexPlus.obj K := sorry

/-- Morphismwise computation for the bounded-below finite filtered quotient cochain functor. -/
@[simp]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (cochain C p).map f = (functor C p).mapCochainComplexPlus.map f := sorry

end cochain

end CategoryTheory.FilteredObject.Finite.Quotient
