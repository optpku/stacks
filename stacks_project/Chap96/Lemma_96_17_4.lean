/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoFibreProduct.Faithful
public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoFibreProduct.Equalizers
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
import StacksCheckRecall

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

section Faithful

variable (f : X ⟶ Y) (g : Z ⟶ Y)
variable [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)]

/- Lemma 96.17.4 (1): if `f : X ⟶ Y` and `g : Z ⟶ Y` are faithful 1-morphisms
of categories fibred in groupoids over `(Sch/S)_fppf`, then the functor
`X ×_Y Z ⟶ Y` given by `TwoFibreProduct.fst f g ≫ f` is faithful. -/
@[stacks 06X0] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct.toBase_faithful f g :
    Functor.Faithful (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≫ f)))

end Faithful

section Equalizers

variable (f : X ⟶ Y) (g : Z ⟶ Y)
variable [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)]
variable [HasEqualizers X.total] [HasEqualizers Z.total]

/- Lemma 96.17.4 (2): if `f : X ⟶ Y` and `g : Z ⟶ Y` are faithful 1-morphisms
of categories fibred in groupoids over `(Sch/S)_fppf` and `X`, `Z` have
equalizers, then so does `X ×_Y Z`. -/
@[stacks 06X0] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct.hasEqualizers f g :
    HasEqualizers (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)))

end Equalizers

end AlgebraicGeometry.GroupoidsOver
