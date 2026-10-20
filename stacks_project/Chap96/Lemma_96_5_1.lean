/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Base change for pushforward of presheaves on categories fibred in groupoids

A two-cartesian square over a scheme gives the canonical base-change isomorphism,
functorial in the presheaf. Pointwise Kan existence records the objectwise limits
used to define the pushforwards at the chosen coefficient universe.
-/

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor total)
open scoped Bicategory

universe u w

/- Lemma 96.5.1: In a two-cartesian square of categories fibred in groupoids over
`S`, there is a canonical isomorphism `g⁻¹ f_* ≅ f'_* (g')⁻¹`, functorial in the
presheaf on `X`. -/
@[stacks 075B] #check (CategoryTheory.FiberedCategoryOver.Groupoids.presheafBaseChangeIso :
  ∀ {S : Scheme.{u}} {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [∀ F : X.totalᵒᵖ ⥤ Type w, Functor.HasPointwiseRightKanExtension (toFunctor f).op F]
    [∀ F : (total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w,
      Functor.HasPointwiseRightKanExtension
        (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op F],
    ((toFunctor f).op.ran : (X.totalᵒᵖ ⥤ Type w) ⥤ (Y.totalᵒᵖ ⥤ Type w)) ⋙
        Functor.presheafInverseImage (toFunctor g) (Type w) ≅
      Functor.presheafInverseImage
          (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f)) (Type w) ⋙
        ((toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)).op.ran :
          ((total (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f))ᵒᵖ ⥤ Type w) ⥤
            (Y'.totalᵒᵖ ⥤ Type w)))
