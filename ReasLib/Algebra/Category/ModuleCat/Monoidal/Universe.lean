/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe uR uM

namespace ModuleCat

variable (R : Type uR) [CommRing R]

/-- The tensor product and ULift unit give the usual monoidal data on modules
whose universe is at least the universe of the coefficient ring. -/
instance instMonoidalCategoryStructMax :
    MonoidalCategoryStruct (ModuleCat.{max uR uM} R) where
  tensorObj M N := of R (TensorProduct R M N)
  whiskerLeft M _ _ f := ofHom <| f.hom.lTensor M
  whiskerRight f M := ofHom <| f.hom.rTensor M
  tensorHom f g := ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := of R (ULift.{uM, uR} R)
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M :=
    (((TensorProduct.congr
          (ULift.moduleEquiv : ULift.{uM, uR} R ≃ₗ[R] R)
          (LinearEquiv.refl R M)).trans
        (TensorProduct.lid R M)).toModuleIso)
  rightUnitor M :=
    (((TensorProduct.congr
          (LinearEquiv.refl R M)
          (ULift.moduleEquiv : ULift.{uM, uR} R ≃ₗ[R] R)).trans
        (TensorProduct.rid R M)).toModuleIso)

namespace MonoidalCategoryMax

/-- Tensoring morphisms factors as right and left whiskering. -/
theorem tensorHom_def {X₁ Y₁ X₂ Y₂ : ModuleCat.{max uR uM} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := sorry

/-- Tensor products preserve identities. -/
theorem id_tensorHom_id : ∀ X₁ X₂ : ModuleCat.{max uR uM} R, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂) := sorry

/-- Tensor products preserve composition in both variables. -/
theorem tensorHom_comp_tensorHom :
    ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat.{max uR uM} R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := sorry

/-- Left whiskering preserves identities. -/
theorem whiskerLeft_id : ∀ (X Y : ModuleCat.{max uR uM} R), X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := sorry

/-- Right whiskering preserves identities. -/
theorem id_whiskerRight : ∀ (X Y : ModuleCat.{max uR uM} R), 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := sorry

/-- Tensor associators are natural in all three variables. -/
theorem associator_naturality :
    ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat.{max uR uM} R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := sorry

/-- The left tensor unitor is natural. -/
theorem leftUnitor_naturality :
    ∀ {X Y : ModuleCat.{max uR uM} R} (f : X ⟶ Y), 𝟙_ _ ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := sorry

/-- The right tensor unitor is natural. -/
theorem rightUnitor_naturality :
    ∀ {X Y : ModuleCat.{max uR uM} R} (f : X ⟶ Y), f ▷ 𝟙_ _ ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := sorry

/-- Tensor associators satisfy the pentagon identity. -/
theorem pentagon :
    ∀ W X Y Z : ModuleCat.{max uR uM} R,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := sorry

/-- Tensor unitors and associators satisfy the triangle identity. -/
theorem triangle :
    ∀ X Y : ModuleCat.{max uR uM} R, (α_ X (𝟙_ _) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := sorry

end MonoidalCategoryMax

/-- Modules at the maximum of the ring and carrier universes form a monoidal category
with ordinary tensor products and a universe-lifted regular module as unit. -/
instance instMonoidalCategoryMax : MonoidalCategory (ModuleCat.{max uR uM} R) where
  tensorHom_def := MonoidalCategoryMax.tensorHom_def R
  id_tensorHom_id := MonoidalCategoryMax.id_tensorHom_id R
  tensorHom_comp_tensorHom := MonoidalCategoryMax.tensorHom_comp_tensorHom R
  whiskerLeft_id := MonoidalCategoryMax.whiskerLeft_id R
  id_whiskerRight := MonoidalCategoryMax.id_whiskerRight R
  associator_naturality := MonoidalCategoryMax.associator_naturality R
  leftUnitor_naturality := MonoidalCategoryMax.leftUnitor_naturality R
  rightUnitor_naturality := MonoidalCategoryMax.rightUnitor_naturality R
  pentagon := MonoidalCategoryMax.pentagon R
  triangle := MonoidalCategoryMax.triangle R

namespace MonoidalCategoryMax

/-- The tensor object is the ordinary module tensor product. -/
theorem tensorObj (M N : ModuleCat.{max uR uM} R) :
    M ⊗ N = of R (TensorProduct R M N) := rfl

/-- Tensor morphisms are the tensor products of linear maps. -/
theorem tensorHom {M N P Q : ModuleCat.{max uR uM} R}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := rfl

/-- The tensor unit is the universe-lifted regular module. -/
theorem tensorUnit :
    𝟙_ (ModuleCat.{max uR uM} R) = of R (ULift.{uM, uR} R) := rfl

/-- Left whiskering is tensoring a linear map on the left. -/
theorem hom_whiskerLeft (M : ModuleCat.{max uR uM} R)
    {N P : ModuleCat.{max uR uM} R} (f : N ⟶ P) :
    (M ◁ f).hom = f.hom.lTensor M := rfl

/-- Right whiskering is tensoring a linear map on the right. -/
theorem hom_whiskerRight {M N : ModuleCat.{max uR uM} R}
    (f : M ⟶ N) (P : ModuleCat.{max uR uM} R) :
    (f ▷ P).hom = f.hom.rTensor P := rfl

/-- Tensoring modules is additive in both variables. -/
instance monoidalPreadditive : MonoidalPreadditive (ModuleCat.{max uR uM} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp [hom_whiskerLeft, hom_whiskerRight]

end MonoidalCategoryMax

end ModuleCat
