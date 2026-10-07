module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor/internal-Hom comparison

This leaf constructs the left-tensor comparison directly from currying, the braiding, and
evaluation.  The resulting API uses the standard `ihom` spelling and does not expose a bundled
choice of right internal Hom.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The canonical morphism obtained by tensoring an internal Hom on the left. -/
@[stacks 0BYS "tensor/internal-Hom comparison"]
noncomputable def tensorInternalHomComparison (K L M : C) :
    K ⊗ (ihom M).obj L ⟶ (ihom M).obj (K ⊗ L) :=
  curry
    ((α_ M K ((ihom M).obj L)).inv ≫
      (β_ M K).hom ▷ (ihom M).obj L ≫
      (α_ K M ((ihom M).obj L)).hom ≫
      K ◁ (ihom.ev M).app L)

/-- The uncurried form of `tensorInternalHomComparison` is the canonical reassociation, braiding,
and evaluation composite. -/
@[stacks 0BYS "tensor/internal-Hom evaluation specification"]
theorem tensorInternalHomComparison_uncurry (K L M : C) :
    uncurry (tensorInternalHomComparison K L M) =
      (α_ M K ((ihom M).obj L)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L ≫
        (α_ K M ((ihom M).obj L)).hom ≫
        K ◁ (ihom.ev M).app L := sorry

/-- The tensor/internal-Hom comparison is natural in the tensor factor. -/
@[stacks 0BYS "tensor/internal-Hom tensor naturality"]
theorem tensorInternalHomComparison_natural_tensor
    {K₁ K₂ L M : C} (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 ((ihom M).obj L))
      (tensorInternalHomComparison K₁ L M)
      (tensorInternalHomComparison K₂ L M)
      ((ihom M).map (fK ⊗ₘ 𝟙 L)) := sorry

/-- The tensor/internal-Hom comparison is natural in the target of the internal Hom. -/
@[stacks 0BYS "tensor/internal-Hom target naturality"]
theorem tensorInternalHomComparison_natural_target
    (K M : C) {L₁ L₂ : C} (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihom M).map fL)
      (tensorInternalHomComparison K L₁ M)
      (tensorInternalHomComparison K L₂ M)
      ((ihom M).map (𝟙 K ⊗ₘ fL)) := sorry

/-- The tensor/internal-Hom comparison is contravariantly natural in its internal-Hom source. -/
@[stacks 0BYS "tensor/internal-Hom source naturality"]
theorem tensorInternalHomComparison_natural_source
    (K L : C) {M₁ M₂ : C} (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (pre fM).app L)
      (tensorInternalHomComparison K L M₂)
      (tensorInternalHomComparison K L M₁)
      ((pre fM).app (K ⊗ L)) := sorry

/- The three variance directions compose into one square, which is the convenient form for
transporting a comparison through simultaneous maps in all variables. -/
@[stacks 0BYS "tensor/internal-Hom simultaneous naturality"]
theorem tensorInternalHomComparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL))
      (tensorInternalHomComparison K₁ L₁ M₂)
      (tensorInternalHomComparison K₂ L₂ M₁)
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := sorry

/-- Tensoring two internal-Hom morphisms gives the canonical morphism
`RHom(K, K') ⊗ RHom(M, M') ⟶ RHom(K ⊗ M, K' ⊗ M')`.

The construction is factored through `tensorInternalHomComparison` and
`internalHomTensorIso`; the final braiding only changes the source order. -/
@[stacks 0FXP "tensor of internal-Hom morphisms"]
noncomputable def tensorHomComparison (K K' M M' : C) :
    (ihom K).obj K' ⊗ (ihom M).obj M' ⟶
      (ihom (K ⊗ M)).obj (K' ⊗ M') :=
  tensorInternalHomComparison ((ihom K).obj K') M' M ≫
    (ihom M).map
      ((β_ ((ihom K).obj K') M').hom ≫
        tensorInternalHomComparison M' K' K ≫
          (ihom K).map (β_ M' K').hom) ≫
    (internalHomTensorIso M K (K' ⊗ M')).hom ≫
    (pre ((β_ K M).hom)).app (K' ⊗ M')

/-- The tensor-of-internal-Homs owner is characterized by its source-order construction. -/
@[stacks 0FXP "tensor of internal-Hom morphisms specification"]
theorem tensorHomComparison_spec (K K' M M' : C) :
    tensorHomComparison K K' M M' =
      tensorInternalHomComparison ((ihom K).obj K') M' M ≫
        (ihom M).map
          ((β_ ((ihom K).obj K') M').hom ≫
            tensorInternalHomComparison M' K' K ≫
              (ihom K).map (β_ M' K').hom) ≫
        (internalHomTensorIso M K (K' ⊗ M')).hom ≫
        (pre ((β_ K M).hom)).app (K' ⊗ M') := sorry

/-- `tensorHomComparison` is contravariantly natural in its first internal-Hom source. -/
@[stacks 0FXP "tensor of internal-Hom morphisms source naturality"]
theorem tensorHomComparison_natural_leftSource
    {K₁ K₂ K' M M' : C} (f : K₁ ⟶ K₂) :
    CommSq
      ((pre f).app K' ⊗ₘ 𝟙 ((ihom M).obj M'))
      (tensorHomComparison K₂ K' M M')
      (tensorHomComparison K₁ K' M M')
      ((pre (f ⊗ₘ 𝟙 M)).app (K' ⊗ M')) := sorry

/-- `tensorHomComparison` is covariantly natural in its first internal-Hom target. -/
@[stacks 0FXP "tensor of internal-Hom morphisms target naturality"]
theorem tensorHomComparison_natural_leftTarget
    (K M M' : C) {K₁' K₂' : C} (f : K₁' ⟶ K₂') :
    CommSq
      ((ihom K).map f ⊗ₘ 𝟙 ((ihom M).obj M'))
      (tensorHomComparison K K₁' M M')
      (tensorHomComparison K K₂' M M')
      ((ihom (K ⊗ M)).map (f ⊗ₘ 𝟙 M')) := sorry

/-- `tensorHomComparison` is contravariantly natural in its second internal-Hom source. -/
@[stacks 0FXP "tensor of internal-Hom morphisms second-source naturality"]
theorem tensorHomComparison_natural_rightSource
    (K K' M' : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    CommSq
      (𝟙 ((ihom K).obj K') ⊗ₘ (pre f).app M')
      (tensorHomComparison K K' M₂ M')
      (tensorHomComparison K K' M₁ M')
      ((pre (𝟙 K ⊗ₘ f)).app (K' ⊗ M')) := sorry

/-- `tensorHomComparison` is covariantly natural in its second internal-Hom target. -/
@[stacks 0FXP "tensor of internal-Hom morphisms second-target naturality"]
theorem tensorHomComparison_natural_rightTarget
    (K K' M : C) {M₁' M₂' : C} (f : M₁' ⟶ M₂') :
    CommSq
      (𝟙 ((ihom K).obj K') ⊗ₘ (ihom M).map f)
      (tensorHomComparison K K' M M₁')
      (tensorHomComparison K K' M M₂')
      ((ihom (K ⊗ M)).map (𝟙 K' ⊗ₘ f)) := sorry

end CategoryTheory.MonoidalClosed
