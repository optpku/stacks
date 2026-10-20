module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Equalizers in two-fibre products of groupoid fibrations

The two-fibre product of faithful morphisms of categories fibred in groupoids has
equalizers whenever both source total categories have equalizers.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct

open Limits
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y Z :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C}

/-- The total category of the two-fibre product of faithful morphisms of categories
fibred in groupoids has equalizers if both source total categories have equalizers. -/
instance hasEqualizers (f : X ⟶ Y) (g : Z ⟶ Y)
    [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)]
    [HasEqualizers X.total] [HasEqualizers Z.total] :
    HasEqualizers (total (CategoryTheory.TwoFibreProduct.apex.{u, v, w, vB} f g)) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct
