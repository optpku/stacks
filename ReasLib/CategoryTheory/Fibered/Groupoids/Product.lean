/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.Naturality
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift

/-!
# Binary products of categories fibred in groupoids

The product over a common base is the two-fibre product of the canonical base projections.
The universal lift of the cone induced by two morphisms gives their product morphism.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]

/-- The binary product of categories fibred in groupoids over `C`, realized as the 2-fibre
product of their canonical projections to the identity fibration. -/
abbrev prod (X Y : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C) :
    FiberedCategoryOver.Groupoids.{u, v, max u v, v} C :=
  TwoFibreProduct.apex X.baseProjection Y.baseProjection

variable {X₁ X₂ Y₁ Y₂ : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}

/-- Two morphisms induce a cone over the base projections of their targets. -/
private noncomputable def prodMap.cone (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    PseudoPullbackCone Y₁.baseProjection Y₂.baseProjection where
  pt := prod X₁ X₂
  fst := TwoFibreProduct.fst X₁.baseProjection X₂.baseProjection ≫ f₁
  snd := TwoFibreProduct.snd X₁.baseProjection X₂.baseProjection ≫ f₂
  iso :=
    (α_ _ _ _) ≪≫
      whiskerLeftIso (TwoFibreProduct.fst X₁.baseProjection X₂.baseProjection)
        (baseProjection.naturality f₁) ≪≫
      TwoFibreProduct.comparisonIso X₁.baseProjection X₂.baseProjection ≪≫
      whiskerLeftIso (TwoFibreProduct.snd X₁.baseProjection X₂.baseProjection)
        (baseProjection.naturality f₂).symm ≪≫
      (α_ _ _ _).symm

/-- The product of 1-morphisms of categories fibred in groupoids, as a 1-morphism
`prod X₁ X₂ ⟶ prod Y₁ Y₂`. -/
noncomputable def prodMap (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prod X₁ X₂ ⟶ prod Y₁ Y₂ :=
  PseudoPullbackCone.lift
    (CategoryTheory.FiberedCategoryOver.Groupoids.prodMap.cone f₁ f₂)
    (TwoFibreProduct.cone Y₁.baseProjection Y₂.baseProjection)

/-- The product 1-morphism commutes with first projections up to the canonical invertible
2-cell. -/
noncomputable def prodMap.fstIso (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prodMap f₁ f₂ ≫ TwoFibreProduct.fst Y₁.baseProjection Y₂.baseProjection ≅
      TwoFibreProduct.fst X₁.baseProjection X₂.baseProjection ≫ f₁ :=
  PseudoPullbackCone.lift.fstIso
    (CategoryTheory.FiberedCategoryOver.Groupoids.prodMap.cone f₁ f₂)
    (TwoFibreProduct.cone Y₁.baseProjection Y₂.baseProjection)

/-- The product 1-morphism commutes with second projections up to the canonical invertible
2-cell. -/
noncomputable def prodMap.sndIso (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    prodMap f₁ f₂ ≫ TwoFibreProduct.snd Y₁.baseProjection Y₂.baseProjection ≅
      TwoFibreProduct.snd X₁.baseProjection X₂.baseProjection ≫ f₂ :=
  PseudoPullbackCone.lift.sndIso
    (CategoryTheory.FiberedCategoryOver.Groupoids.prodMap.cone f₁ f₂)
    (TwoFibreProduct.cone Y₁.baseProjection Y₂.baseProjection)

end CategoryTheory.FiberedCategoryOver.Groupoids
