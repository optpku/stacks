/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
        K ◁ (ihom.ev M).app L := by
  exact uncurry_curry _

set_option backward.isDefEq.respectTransparency false in
/-- The tensor/internal-Hom comparison is natural in the tensor factor. -/
@[stacks 0BYS "tensor/internal-Hom tensor naturality"]
theorem tensorInternalHomComparison_natural_tensor
    {K₁ K₂ L M : C} (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 ((ihom M).obj L))
      (tensorInternalHomComparison K₁ L M)
      (tensorInternalHomComparison K₂ L M)
      ((ihom M).map (fK ⊗ₘ 𝟙 L)) := by
  refine ⟨?_⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  simp only [tensorHom_id, tensorInternalHomComparison_uncurry]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left_assoc, ← whisker_exchange]
  simp only [Category.assoc, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor/internal-Hom comparison is natural in the target of the internal Hom. -/
@[stacks 0BYS "tensor/internal-Hom target naturality"]
theorem tensorInternalHomComparison_natural_target
    (K M : C) {L₁ L₂ : C} (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihom M).map fL)
      (tensorInternalHomComparison K L₁ M)
      (tensorInternalHomComparison K L₂ M)
      ((ihom M).map (𝟙 K ⊗ₘ fL)) := by
  refine ⟨?_⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  simp only [id_tensorHom, tensorInternalHomComparison_uncurry]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp, ihom.ev_naturality,
    whiskerLeft_comp]
  simp only [Category.assoc, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor/internal-Hom comparison is contravariantly natural in its internal-Hom source. -/
@[stacks 0BYS "tensor/internal-Hom source naturality"]
theorem tensorInternalHomComparison_natural_source
    (K L : C) {M₁ M₂ : C} (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (pre fM).app L)
      (tensorInternalHomComparison K L M₂)
      (tensorInternalHomComparison K L M₁)
      ((pre fM).app (K ⊗ L)) := by
  refine ⟨?_⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  simp only [id_tensorHom, tensorInternalHomComparison_uncurry]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp, id_tensor_pre_app_comp_ev,
    whiskerLeft_comp, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]

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
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := by
  have h := ((tensorInternalHomComparison_natural_source K₁ L₁ fM).horiz_comp
    (tensorInternalHomComparison_natural_tensor (L := L₁) (M := M₁) fK)).horiz_comp
    (tensorInternalHomComparison_natural_target K₂ M₁ fL)
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def] using h

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
        (pre ((β_ K M).hom)).app (K' ⊗ M') := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomComparison_curryIso_uncurry (K L M : C) :
    uncurry (internalHomTensorIso K L M).hom =
      (β_ K L).hom ▷ (ihom K).obj ((ihom L).obj M) ≫
        (α_ L K ((ihom K).obj ((ihom L).obj M))).hom ≫
          L ◁ (ihom.ev K).app ((ihom L).obj M) ≫ (ihom.ev L).app M := by
  change uncurry ((Adjunction.rightAdjointUniq (ihom.adjunction (K ⊗ L))
    (tensorLeftTensorAdjunction K L)).inv.app M) = _
  rw [Adjunction.rightAdjointUniq_inv_app]
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (tensorLeftTensorAdjunction K L) (ihom.adjunction (K ⊗ L)) M
  change uncurry _ = _ at h
  rw [h]
  simp [tensorLeftTensorAdjunction, Adjunction.ofNatIsoLeft]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomComparison_curryIso_natural_left
    {K K' L M : C} (f : K ⟶ K') :
    (pre f).app ((ihom L).obj M) ≫ (internalHomTensorIso K L M).hom =
      (internalHomTensorIso K' L M).hom ≫ (pre (f ▷ L)).app M := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  simp only [tensorHomComparison_curryIso_uncurry]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev, whiskerLeft_comp_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomComparison_curryIso_natural_middle
    (K : C) {L L' M : C} (f : L ⟶ L') :
    (ihom K).map ((pre f).app M) ≫ (internalHomTensorIso K L M).hom =
      (internalHomTensorIso K L' M).hom ≫ (pre (K ◁ f)).app M := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  simp only [tensorHomComparison_curryIso_uncurry]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, ihom.ev_naturality, whiskerLeft_comp_assoc,
    id_tensor_pre_app_comp_ev, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left_assoc]
  congr 2
  exact whisker_exchange_assoc f ((ihom.ev K).app ((ihom L').obj M))
    ((ihom.ev L').app M)

set_option backward.isDefEq.respectTransparency false in
/-- `tensorHomComparison` is contravariantly natural in its first internal-Hom source. -/
@[stacks 0FXP "tensor of internal-Hom morphisms source naturality"]
theorem tensorHomComparison_natural_leftSource
    {K₁ K₂ K' M M' : C} (f : K₁ ⟶ K₂) :
    CommSq
      ((pre f).app K' ⊗ₘ 𝟙 ((ihom M).obj M'))
      (tensorHomComparison K₂ K' M M')
      (tensorHomComparison K₁ K' M M')
      ((pre (f ⊗ₘ 𝟙 M)).app (K' ⊗ M')) := by
  have ht := (tensorInternalHomComparison_natural_source M' K' f).w
  simp only [id_tensorHom] at ht
  have hi : CommSq
      ((pre f).app K' ▷ M')
      ((β_ ((ihom K₂).obj K') M').hom ≫
        tensorInternalHomComparison M' K' K₂ ≫ (ihom K₂).map (β_ M' K').hom)
      ((β_ ((ihom K₁).obj K') M').hom ≫
        tensorInternalHomComparison M' K' K₁ ≫ (ihom K₁).map (β_ M' K').hom)
      ((pre f).app (K' ⊗ M')) := by
    refine ⟨?_⟩
    rw [BraidedCategory.braiding_naturality_left_assoc, reassoc_of% ht]
    rw [← (pre f).naturality (β_ M' K').hom]
    simp only [Category.assoc]
  have h := tensorInternalHomComparison_natural_tensor (M := M) (L := M')
    ((pre f).app K')
  simp only [tensorHom_id] at h
  have hIso := CommSq.mk (tensorHomComparison_curryIso_natural_middle M
    (M := K' ⊗ M') f)
  have hPre : CommSq
      ((pre (M ◁ f)).app (K' ⊗ M'))
      ((pre (β_ K₂ M).hom).app (K' ⊗ M'))
      ((pre (β_ K₁ M).hom).app (K' ⊗ M'))
      ((pre (f ▷ M)).app (K' ⊗ M')) := by
    refine ⟨?_⟩
    simp only [← NatTrans.comp_app, ← pre_map]
    rw [BraidedCategory.braiding_naturality_left]
  simpa only [tensorHom_id, tensorHomComparison, Category.assoc] using
    h.vert_comp ((hi.map (ihom M)).vert_comp (hIso.vert_comp hPre))

set_option backward.isDefEq.respectTransparency false in
/-- `tensorHomComparison` is covariantly natural in its first internal-Hom target. -/
@[stacks 0FXP "tensor of internal-Hom morphisms target naturality"]
theorem tensorHomComparison_natural_leftTarget
    (K M M' : C) {K₁' K₂' : C} (f : K₁' ⟶ K₂') :
    CommSq
      ((ihom K).map f ⊗ₘ 𝟙 ((ihom M).obj M'))
      (tensorHomComparison K K₁' M M')
      (tensorHomComparison K K₂' M M')
      ((ihom (K ⊗ M)).map (f ⊗ₘ 𝟙 M')) := by
  have ht := (tensorInternalHomComparison_natural_target M' K f).w
  simp only [id_tensorHom] at ht
  have hi : CommSq
      ((ihom K).map f ▷ M')
      ((β_ ((ihom K).obj K₁') M').hom ≫
        tensorInternalHomComparison M' K₁' K ≫ (ihom K).map (β_ M' K₁').hom)
      ((β_ ((ihom K).obj K₂') M').hom ≫
        tensorInternalHomComparison M' K₂' K ≫ (ihom K).map (β_ M' K₂').hom)
      ((ihom K).map (f ▷ M')) := by
    refine ⟨?_⟩
    rw [BraidedCategory.braiding_naturality_left_assoc, reassoc_of% ht]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [BraidedCategory.braiding_naturality_right]
  have h := tensorInternalHomComparison_natural_tensor (M := M) (L := M')
    ((ihom K).map f)
  simp only [tensorHom_id] at h
  have hIso := CommSq.mk (internalHomTensorIso_natural_right M K (f ▷ M'))
  have hPre := CommSq.mk ((pre (β_ K M).hom).naturality (f ▷ M'))
  simpa only [tensorHom_id, tensorHomComparison, Category.assoc] using
    h.vert_comp ((hi.map (ihom M)).vert_comp (hIso.vert_comp hPre))

set_option backward.isDefEq.respectTransparency false in
/-- `tensorHomComparison` is contravariantly natural in its second internal-Hom source. -/
@[stacks 0FXP "tensor of internal-Hom morphisms second-source naturality"]
theorem tensorHomComparison_natural_rightSource
    (K K' M' : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    CommSq
      (𝟙 ((ihom K).obj K') ⊗ₘ (pre f).app M')
      (tensorHomComparison K K' M₂ M')
      (tensorHomComparison K K' M₁ M')
      ((pre (𝟙 K ⊗ₘ f)).app (K' ⊗ M')) := by
  let g := (β_ ((ihom K).obj K') M').hom ≫
    tensorInternalHomComparison M' K' K ≫ (ihom K).map (β_ M' K').hom
  have h := tensorInternalHomComparison_natural_source ((ihom K).obj K') M' f
  simp only [id_tensorHom] at h
  have hi := CommSq.mk ((pre f).naturality g).symm
  have hIso := CommSq.mk (tensorHomComparison_curryIso_natural_left
    (L := K) (M := K' ⊗ M') f)
  have hPre : CommSq
      ((pre (f ▷ K)).app (K' ⊗ M'))
      ((pre (β_ K M₂).hom).app (K' ⊗ M'))
      ((pre (β_ K M₁).hom).app (K' ⊗ M'))
      ((pre (K ◁ f)).app (K' ⊗ M')) := by
    refine ⟨?_⟩
    simp only [← NatTrans.comp_app, ← pre_map]
    rw [BraidedCategory.braiding_naturality_right]
  simpa only [id_tensorHom, tensorHomComparison, Category.assoc, g] using
    h.vert_comp (hi.vert_comp (hIso.vert_comp hPre))

set_option backward.isDefEq.respectTransparency false in
/-- `tensorHomComparison` is covariantly natural in its second internal-Hom target. -/
@[stacks 0FXP "tensor of internal-Hom morphisms second-target naturality"]
theorem tensorHomComparison_natural_rightTarget
    (K K' M : C) {M₁' M₂' : C} (f : M₁' ⟶ M₂') :
    CommSq
      (𝟙 ((ihom K).obj K') ⊗ₘ (ihom M).map f)
      (tensorHomComparison K K' M M₁')
      (tensorHomComparison K K' M M₂')
      ((ihom (K ⊗ M)).map (𝟙 K' ⊗ₘ f)) := by
  have ht := (tensorInternalHomComparison_natural_tensor (L := K') (M := K) f).w
  simp only [tensorHom_id] at ht
  have hi : CommSq
      (((ihom K).obj K') ◁ f)
      ((β_ ((ihom K).obj K') M₁').hom ≫
        tensorInternalHomComparison M₁' K' K ≫ (ihom K).map (β_ M₁' K').hom)
      ((β_ ((ihom K).obj K') M₂').hom ≫
        tensorInternalHomComparison M₂' K' K ≫ (ihom K).map (β_ M₂' K').hom)
      ((ihom K).map (K' ◁ f)) := by
    refine ⟨?_⟩
    rw [BraidedCategory.braiding_naturality_right_assoc, reassoc_of% ht]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [BraidedCategory.braiding_naturality_left]
  have h := tensorInternalHomComparison_natural_target ((ihom K).obj K') M f
  simp only [id_tensorHom] at h
  have hIso := CommSq.mk (internalHomTensorIso_natural_right M K (K' ◁ f))
  have hPre := CommSq.mk ((pre (β_ K M).hom).naturality (K' ◁ f))
  simpa only [id_tensorHom, tensorHomComparison, Category.assoc] using
    h.vert_comp ((hi.map (ihom M)).vert_comp (hIso.vert_comp hPre))

end CategoryTheory.MonoidalClosed
