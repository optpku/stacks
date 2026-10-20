/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Faithfulness of two-fibre products of groupoid fibrations

The canonical functor from a two-fibre product of faithful morphisms to their common
target is faithful.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y Z :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C}

/-- The canonical functor from the two-fibre product of two faithful morphisms of
categories fibred in groupoids to their common target is faithful. -/
instance toBase_faithful (f : X ⟶ Y) (g : Z ⟶ Y)
    [Functor.Faithful (toFunctor f)] [Functor.Faithful (toFunctor g)] :
    Functor.Faithful
      (toFunctor (CategoryTheory.TwoFibreProduct.fst.{u, v, w, vB} f g ≫ f)) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.TwoFibreProduct
