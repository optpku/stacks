module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient

/-!
# Filtration quotients of bounded-below finite filtered complexes

Quotient-by-`F^p` evaluation restricts to finite filtered objects and lifts canonically to
bounded-below cochain complexes by composition of the existing functors.
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

/-- The finite filtered quotient functor sends an object to its filtration quotient. -/
@[simp]
theorem obj (p : ℤ) (X : FilteredObject.Finite.category C) :
    (functor C p).obj X = X.obj.quotient p := sorry

/-- The finite filtered quotient functor sends a morphism to its induced quotient map. -/
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

/-- The quotient cochain functor acts on objects by the bounded-below lift of quotient
evaluation. -/
@[simp]
theorem obj (p : ℤ)
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    (cochain C p).obj K = (functor C p).mapCochainComplexPlus.obj K := sorry

/-- The quotient cochain functor acts on morphisms by the bounded-below lift of quotient
evaluation. -/
@[simp]
theorem map (p : ℤ)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    (cochain C p).map f = (functor C p).mapCochainComplexPlus.map f := sorry

end cochain

end CategoryTheory.FilteredObject.Finite.Quotient
