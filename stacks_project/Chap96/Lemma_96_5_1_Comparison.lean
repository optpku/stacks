/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.BaseChange

/-!
# Inverse-image comparison for a two-fibre product

The canonical inverse-image square is available from the shared presheaf
base-change owner.
-/

open CategoryTheory
open FiberedCategoryOver.Groupoids (toFunctor)
open scoped Bicategory

universe u v uT vT w

#check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafInverseImage_twoFibreIso :
  ∀ {C : Type u} [Category.{v} C]
    {X Y Y' : FiberedCategoryOver.Groupoids.{u, v, max uT (max u (max v vT)), max v vT} C}
    (f : X ⟶ Y) (g : Y' ⟶ Y),
    Functor.presheafInverseImage (toFunctor g) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.fst.{u, v, uT, vT} g f)) (Type w) ≅
    Functor.presheafInverseImage (toFunctor f) (Type w) ⋙
      Functor.presheafInverseImage
        (toFunctor (TwoFibreProduct.snd.{u, v, uT, vT} g f)) (Type w))
