module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Two-fibre products of faithful groupoid fibrations

Faithful 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf` remain
faithful after 2-fibre product over the common target. If both source fibrations
have equalizers, so does the 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S}

/-- Lemma 96.17.4 (1): if `f : X ⟶ Y` and `g : Z ⟶ Y` are faithful 1-morphisms
of categories fibred in groupoids over `(Sch/S)_fppf`, then the functor
`X ×_Y Z ⟶ Y` given by `TwoFibreProduct.fst f g ≫ f` is faithful. -/
@[stacks 06X0]
instance twoFibreProduct_toBase_faithful (f : X ⟶ Y) (g : Z ⟶ Y)
    [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)] :
    Functor.Faithful (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≫ f)) := sorry

/-- Lemma 96.17.4 (2): if `f : X ⟶ Y` and `g : Z ⟶ Y` are faithful 1-morphisms
of categories fibred in groupoids over `(Sch/S)_fppf` and `X`, `Z` have
equalizers, then so does `X ×_Y Z`. -/
@[stacks 06X0]
instance twoFibreProduct_hasEqualizers (f : X ⟶ Y) (g : Z ⟶ Y)
    [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)]
    [HasEqualizers X.total] [HasEqualizers Z.total] :
    HasEqualizers (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

end AlgebraicGeometry.GroupoidsOver
