module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CostructuredArrow
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize.Universal

/-!
# Bilimit property of costructured-arrow projection squares
-/

@[expose] public section

open CategoryTheory

universe uA vA uC vC uD vD

namespace CategoryTheory.Limits.CategoricalPullback.CostructuredArrow

variable {A : Type uA} [Category.{vA} A]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The projection square of the costructured arrow of a composite functor is a resized
bilimit. -/
instance instSquareIsBilimit (F : A ⥤ C) (G : C ⥤ D) (d : D) :
    CatCommSqOver.Resized.IsBilimit (square F G d) :=
  CatCommSqOver.Resized.isBilimitOfComparisonEquivalence
    (square F G d) (equivalence F G d) (Iso.refl _)

end CategoryTheory.Limits.CategoricalPullback.CostructuredArrow
