/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.ExplicitCore
public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import Mathlib.Tactic.CrossRefAttribute
@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory
noncomputable section
universe v u
namespace CategoryTheory.MonoidalClosed

/-- The enriched composition morphism selected by an explicit closed-monoidal owner. -/
@[stacks 0A8J "explicit closed-owner internal-Hom composition"]
noncomputable abbrev compOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (ihomOf H K).obj L ⊗ (ihomOf H L).obj M ⟶ (ihomOf H K).obj M :=
  @comp C _ _ K L M (@MonoidalClosed.closed C _ _ H K)
    (@MonoidalClosed.closed C _ _ H L)

/-- Specification of the direct explicit-owner internal-Hom composition. -/
@[stacks 0A8J "explicit closed-owner internal-Hom composition specification"]
theorem compOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    compOf H K L M =
      @comp C _ _ K L M (@MonoidalClosed.closed C _ _ H K)
        (@MonoidalClosed.closed C _ _ H L) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit-owner composition is covariantly natural in its target object. -/
@[reassoc, stacks 0A8J "explicit closed-owner composition target naturality"]
theorem compOf_natural_target
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (𝟙 ((ihomOf H K).obj L) ⊗ₘ (ihomOf H L).map f) ≫
        compOf H K L M₂ =
      compOf H K L M₁ ≫ (ihomOf H K).map f := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  change (𝟙 ((ihom K).obj L) ⊗ₘ (ihom L).map f) ≫ comp K L M₂ =
    comp K L M₁ ≫ (ihom K).map f
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left]
  simp only [comp_eq]
  rw [uncurry_curry]
  rw [uncurry_ihom_map]
  simp only [whiskerLeft_curry_ihom_ev_app_assoc, compTranspose_eq]
  simp only [id_tensorHom, Functor.id_obj, Functor.comp_obj, curriedTensor_obj_obj,
    Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ihom.ev_naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit-owner composition is contravariantly natural in its source object. -/
@[reassoc, stacks 0A8J "explicit closed-owner composition source naturality"]
theorem compOf_natural_source
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K K' L M : C} (f : K ⟶ K') :
    ((preOf H f).app L ⊗ₘ 𝟙 ((ihomOf H L).obj M)) ≫
        compOf H K L M =
      compOf H K' L M ≫ (preOf H f).app M := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  change ((pre f).app L ⊗ₘ 𝟙 ((ihom L).obj M)) ≫ comp K L M =
    comp K' L M ≫ (pre f).app M
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  simp only [comp_eq]
  rw [uncurry_curry, uncurry_curry]
  simp only [compTranspose_eq]
  rw [tensorHom_id, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev,
    comp_whiskerRight_assoc, associator_inv_naturality_left_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit-owner composition has opposite variance in its middle object. -/
@[reassoc, stacks 0A8J "explicit closed-owner composition middle naturality"]
theorem compOf_natural_middle
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K : C) {L L' M : C} (g : L ⟶ L') :
    (𝟙 ((ihomOf H K).obj L) ⊗ₘ (preOf H g).app M) ≫
        compOf H K L M =
      ((ihomOf H K).map g ⊗ₘ 𝟙 ((ihomOf H L').obj M)) ≫
        compOf H K L' M := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  change (𝟙 ((ihom K).obj L) ⊗ₘ (pre g).app M) ≫ comp K L M =
    ((ihom K).map g ⊗ₘ 𝟙 ((ihom L').obj M)) ≫ comp K L' M
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left]
  simp only [comp_eq]
  rw [uncurry_curry, uncurry_curry]
  simp only [compTranspose_eq]
  rw [id_tensorHom, tensorHom_id,
    associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc]
  simp only [Functor.id_obj]
  rw [id_tensor_pre_app_comp_ev,
    ← comp_whiskerRight_assoc, ← ihom.ev_naturality,
    comp_whiskerRight_assoc]

namespace Source

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C]

/-- The source-order internal-Hom composition selected by an explicit closed owner.  This is the
instance-free counterpart of `CategoryTheory.MonoidalClosed.Source.comp`; the braiding puts the
factors in the order `hom(L, M) ⊗ hom(K, L)` used by right-oriented source statements. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91 "explicit source-order internal-Hom composition"]
noncomputable abbrev compOf
    (H : MonoidalClosed C) (K L M : C) :
  (ihomOf H L).obj M ⊗ (ihomOf H K).obj L ⟶ (ihomOf H K).obj M :=
  (β_ ((ihomOf H L).obj M) ((ihomOf H K).obj L)).hom ≫
    @CategoryTheory.MonoidalClosed.comp C _ _ K L M (@MonoidalClosed.closed C _ _ H K)
      (@MonoidalClosed.closed C _ _ H L)

/-- The explicit source-order composition is the braiding transport of `compOf`. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91 "explicit source-order internal-Hom composition specification"]
theorem compOf_spec (H : MonoidalClosed C) (K L M : C) :
    compOf H K L M =
      (β_ ((ihomOf H L).obj M) ((ihomOf H K).obj L)).hom ≫
        @CategoryTheory.MonoidalClosed.comp C _ _ K L M (@MonoidalClosed.closed C _ _ H K)
          (@MonoidalClosed.closed C _ _ H L) := rfl

/-- The explicit source-order composition is covariantly natural in its target. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91 "explicit source-order target naturality"]
theorem compOf_natural_target
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    CommSq
      (((ihomOf H L).map f) ⊗ₘ 𝟙 ((ihomOf H K).obj L))
      (compOf H K L M₁)
      (compOf H K L M₂)
      ((ihomOf H K).map f) :=
  @CategoryTheory.MonoidalClosed.Source.comp_natural_target C _ _ _ H K L M₁ M₂ f

/-- Equality form of `compOf_natural_target`. -/
@[reassoc, stacks 0A8J, stacks 0A8V, stacks 0A91
  "explicit source-order target naturality equation"]
theorem compOf_natural_target_assoc
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (((ihomOf H L).map f) ⊗ₘ 𝟙 ((ihomOf H K).obj L)) ≫
        compOf H K L M₂ =
      compOf H K L M₁ ≫ (ihomOf H K).map f :=
  @CategoryTheory.MonoidalClosed.Source.comp_natural_target_assoc C _ _ _ H K L M₁ M₂ f

/-- The explicit source-order composition is contravariantly natural in its source. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91 "explicit source-order source naturality"]
theorem compOf_natural_source
    (H : MonoidalClosed C) {K K' L M : C} (f : K ⟶ K') :
    CommSq
      (𝟙 ((ihomOf H L).obj M) ⊗ₘ (preOf H f).app L)
      (compOf H K' L M)
      (compOf H K L M)
      ((preOf H f).app M) :=
  @CategoryTheory.MonoidalClosed.Source.comp_natural_source C _ _ _ H K K' L M f

/-- Equality form of `compOf_natural_source`. -/
@[reassoc, stacks 0A8J, stacks 0A8V, stacks 0A91
  "explicit source-order source naturality equation"]
theorem compOf_natural_source_assoc
    (H : MonoidalClosed C) {K K' L M : C} (f : K ⟶ K') :
    (𝟙 ((ihomOf H L).obj M) ⊗ₘ (preOf H f).app L) ≫ compOf H K L M =
      compOf H K' L M ≫ (preOf H f).app M :=
  @CategoryTheory.MonoidalClosed.Source.comp_natural_source_assoc C _ _ _ H K K' L M f

/-- The middle variable has opposite variance on the two internal-Hom factors. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91 "explicit source-order middle naturality"]
theorem compOf_natural_middle
    (H : MonoidalClosed C) (K : C) {L L' M : C} (g : L ⟶ L') :
    ((preOf H g).app M ⊗ₘ 𝟙 ((ihomOf H K).obj L)) ≫ compOf H K L M =
      (𝟙 ((ihomOf H L').obj M) ⊗ₘ (ihomOf H K).map g) ≫ compOf H K L' M :=
  @CategoryTheory.MonoidalClosed.Source.comp_natural_middle C _ _ _ H K L L' M g

end Source

namespace TensorInternalHom

/-- The tensor/internal-Hom comparison selected by an explicit closed-monoidal owner.  This is
the instance-free form of `tensorInternalHomComparison`. -/
@[stacks 0BYN, stacks 0BYS "tensor/internal-Hom comparison from an explicit closed owner"]
noncomputable abbrev comparisonOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    K ⊗ (ihomOf H M).obj L ⟶ (ihomOf H M).obj (K ⊗ L) :=
  @tensorInternalHomComparison C _ _ _ H K L M

/-- The tensor-side transpose defining the explicit-owner tensor/internal-Hom comparison. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom comparison transpose"]
noncomputable def transposeOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    M ⊗ (K ⊗ (ihomOf H M).obj L) ⟶ K ⊗ L :=
  ((adjunctionOf H M).homEquiv _ _).symm (comparisonOf H K L M)

/-- Transposing `comparisonOf` along the explicit-owner tensor/internal-Hom adjunction recovers
`transposeOf`. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom transpose characterization"]
theorem comparisonOf_transpose
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    ((adjunctionOf H M).homEquiv _ _).symm (comparisonOf H K L M) =
      transposeOf H K L M := rfl

/-- The explicit-owner tensor/internal-Hom transpose is reassociation and braiding followed by
evaluation. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom transpose specification"]
theorem transposeOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    transposeOf H K L M =
      (α_ M K ((ihomOf H M).obj L)).inv ≫
        (β_ M K).hom ▷ (ihomOf H M).obj L ≫
          (α_ K M ((ihomOf H M).obj L)).hom ≫
            K ◁ (adjunctionOf H M).counit.app L :=
  @tensorInternalHomComparison_uncurry C _ _ _ H K L M

/-- The explicit-owner tensor/internal-Hom comparison uncurries to reassociation,
braiding, and evaluation. -/
@[stacks 0BYN "explicit tensor/internal-Hom uncurrying specification"]
theorem comparisonOf_uncurry
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    uncurry (comparisonOf H K L M) =
      (α_ M K ((ihomOf H M).obj L)).inv ≫
        (β_ M K).hom ▷ (ihomOf H M).obj L ≫
          (α_ K M ((ihomOf H M).obj L)).hom ≫
            K ◁ (adjunctionOf H M).counit.app L :=
  @tensorInternalHomComparison_uncurry C _ _ _ H K L M

/-- The explicit-owner tensor/internal-Hom comparison is natural in the tensor factor. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom tensor naturality"]
theorem comparisonOf_natural_tensor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L M : C} (fK : K₁ ⟶ K₂) :
    CommSq
      (fK ⊗ₘ 𝟙 ((ihomOf H M).obj L))
      (comparisonOf H K₁ L M)
      (comparisonOf H K₂ L M)
      ((ihomOf H M).map (fK ⊗ₘ 𝟙 L)) :=
  @tensorInternalHomComparison_natural_tensor C _ _ _ H K₁ K₂ L M fK

/-- The explicit-owner tensor/internal-Hom comparison is natural in the internal-Hom target. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom target naturality"]
theorem comparisonOf_natural_target
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K M : C) {L₁ L₂ : C} (fL : L₁ ⟶ L₂) :
    CommSq
      (𝟙 K ⊗ₘ (ihomOf H M).map fL)
      (comparisonOf H K L₁ M)
      (comparisonOf H K L₂ M)
      ((ihomOf H M).map (𝟙 K ⊗ₘ fL)) :=
  @tensorInternalHomComparison_natural_target C _ _ _ H K M L₁ L₂ fL

/-- The explicit-owner tensor/internal-Hom comparison is contravariantly natural in the
internal-Hom source. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom source naturality"]
theorem comparisonOf_natural_source
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (fM : M₁ ⟶ M₂) :
    CommSq
      (𝟙 K ⊗ₘ (preOf H fM).app L)
      (comparisonOf H K L M₂)
      (comparisonOf H K L M₁)
      ((preOf H fM).app (K ⊗ L)) :=
  @tensorInternalHomComparison_natural_source C _ _ _ H K L M₁ M₂ fM

/-- Simultaneous naturality of the explicit-owner tensor/internal-Hom comparison in all three
variables. -/
@[stacks 0BYN, stacks 0BYS "explicit tensor/internal-Hom simultaneous naturality"]
theorem comparisonOf_natural
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((preOf H fM).app L₁ ≫ (ihomOf H M₁).map fL))
      (comparisonOf H K₁ L₁ M₂)
      (comparisonOf H K₂ L₂ M₁)
      ((preOf H fM).app (K₁ ⊗ L₁) ≫
        (ihomOf H M₁).map (fK ⊗ₘ fL)) :=
  @tensorInternalHomComparison_natural C _ _ _ H K₁ K₂ L₁ L₂ M₁ M₂ fK fL fM

/-- The tensor/internal-Hom unit selected by an explicit closed-monoidal
owner. -/
@[stacks 0A6B, stacks 0A8W "explicit tensor/internal-Hom unit"]
noncomputable abbrev unitOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) :
    K ⟶ (ihomOf H L).obj (K ⊗ L) :=
  @tensorInternalHomUnit C _ _ _ H K L

/-- The explicit-owner tensor/internal-Hom unit is coevaluation followed by transport along the
braiding. -/
@[stacks 0A6B, stacks 0A8W "explicit tensor/internal-Hom unit specification"]
theorem unitOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) :
    unitOf H K L =
      (adjunctionOf H L).unit.app K ≫
        (ihomOf H L).map (β_ L K).hom :=
  @tensorInternalHomUnit_spec C _ _ _ H K L

/-- The explicit-owner tensor/internal-Hom unit is natural in its tensor input. -/
@[reassoc, stacks 0A6B, stacks 0A8W "explicit tensor/internal-Hom unit input naturality"]
theorem unitOf_natural_left
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (L : C) {K₁ K₂ : C} (f : K₁ ⟶ K₂) :
    f ≫ unitOf H K₂ L =
      unitOf H K₁ L ≫ (ihomOf H L).map (f ▷ L) :=
  (@tensorInternalHomUnit_natural_left C _ _ _ H K₁ K₂ L f).w

/-- The explicit-owner tensor/internal-Hom unit is contravariantly/covariantly natural in its
right tensor parameter. -/
@[reassoc, stacks 0A6B, stacks 0A8W "explicit tensor/internal-Hom unit parameter naturality"]
theorem unitOf_natural_right
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K : C) {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    unitOf H K L₂ ≫ (preOf H f).app (K ⊗ L₂) =
      unitOf H K L₁ ≫ (ihomOf H L₁).map (K ◁ f) :=
  (@tensorInternalHomUnit_natural_right C _ _ _ H K L₁ L₂ f).w

/-- The evaluation counit selected by an explicit closed-monoidal owner. -/
@[stacks 0A8W "explicit tensor/internal-Hom counit"]
noncomputable abbrev counitOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (E N : C) :
    E ⊗ (ihomOf H E).obj N ⟶ N :=
  (adjunctionOf H E).counit.app N

/-- The explicit-owner tensor/internal-Hom counit is natural in its target object. -/
@[reassoc, stacks 0A8W "explicit tensor/internal-Hom counit target naturality"]
theorem counitOf_natural_target
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (E : C) {N₁ N₂ : C} (f : N₁ ⟶ N₂) :
    (𝟙 E ⊗ₘ (ihomOf H E).map f) ≫ counitOf H E N₂ =
      counitOf H E N₁ ≫ f :=
  by
    -- Local instance justification (defeq pin): pin the `Closed E` structure selected by the
    -- explicit owner `H` for the definitional counit computation in this proof.
    letI : Closed E := @MonoidalClosed.closed C _ _ H E
    rw [id_tensorHom]
    change E ◁ (ihom E).map f ≫ (ihom.ev E).app N₂ = (ihom.ev E).app N₁ ≫ f
    exact ihom.ev_naturality E f

/-- The explicit-owner tensor/internal-Hom counit is naturally compatible with changing its
source parameter. -/
@[reassoc, stacks 0A8W "explicit tensor/internal-Hom counit source naturality"]
theorem counitOf_natural_source
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {E₁ E₂ : C} (f : E₁ ⟶ E₂) (N : C) :
    (f ⊗ₘ 𝟙 ((ihomOf H E₂).obj N)) ≫ counitOf H E₂ N =
      (𝟙 E₁ ⊗ₘ (preOf H f).app N) ≫ counitOf H E₁ N :=
  by
    -- Local instance justification (defeq pin): pin the `Closed E₂` structure selected by the
    -- explicit owner `H` for the definitional counit computation in this proof.
    letI : Closed E₂ := @MonoidalClosed.closed C _ _ H E₂
    -- Local instance justification (defeq pin): pin the `Closed E₁` structure selected by the
    -- explicit owner `H` for the definitional counit computation in this proof.
    letI : Closed E₁ := @MonoidalClosed.closed C _ _ H E₁
    rw [tensorHom_id, id_tensorHom]
    change f ▷ (ihom E₂).obj N ≫ (ihom.ev E₂).app N =
      E₁ ◁ (pre f).app N ≫ (ihom.ev E₁).app N
    exact (id_tensor_pre_app_comp_ev f N).symm

end TensorInternalHom

namespace InternalHomTensor

/-- The functor-level iterated internal-Hom/tensor-source isomorphism selected by an
explicit closed-monoidal owner.  This is the instance-free form of
`InternalHomTensor.natIso`. -/
@[stacks 0A65, stacks 01CN, stacks 03EO, stacks 08DJ
  "functor-level internal-Hom tensor-source isomorphism from an explicit owner"]
noncomputable abbrev natIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) :
    ihomOf H L ⋙ ihomOf H K ≅ ihomOf H (K ⊗ L) :=
  @CategoryTheory.MonoidalClosed.InternalHomTensor.natIso C _ _ _ H K L

/-- The iterated internal-Hom/tensor-source isomorphism selected by an explicit
closed-monoidal owner.  This is the instance-free form of `internalHomTensorIso`. -/
@[stacks 0A65, stacks 01CN, stacks 03EO, stacks 08DJ "internal-Hom tensor-source isomorphism from an explicit owner"]
noncomputable abbrev isoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (ihomOf H K).obj ((ihomOf H L).obj M) ≅ (ihomOf H (K ⊗ L)).obj M :=
  (natIsoOf H K L).app M

/-- The component of the explicit-owner functor-level comparison is `isoOf`. -/
@[simp, stacks 0A65 "explicit internal-Hom tensor-source component"]
theorem natIsoOf_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (natIsoOf H K L).app M = isoOf H K L M := rfl

/-- The forward component of `natIsoOf` is the forward map of `isoOf`. -/
@[simp, stacks 0A65 "explicit internal-Hom tensor-source hom component"]
theorem natIsoOf_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (natIsoOf H K L).hom.app M = (isoOf H K L M).hom := rfl

/-- The inverse component of `natIsoOf` is the inverse map of `isoOf`. -/
@[simp, stacks 0A65 "explicit internal-Hom tensor-source inverse component"]
theorem natIsoOf_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (natIsoOf H K L).inv.app M = (isoOf H K L M).inv := rfl

/-- The explicit-owner internal-Hom tensor-source isomorphism is contravariantly natural in its
left tensor factor. -/
@[stacks 03EO "explicit internal-Hom tensor-source left naturality"]
theorem isoOf_natural_left
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L M : C} (f : K₁ ⟶ K₂) :
    (preOf H f).app ((ihomOf H L).obj M) ≫ (isoOf H K₁ L M).hom =
      (isoOf H K₂ L M).hom ≫ (preOf H (f ▷ L)).app M :=
  @internalHomTensorIso_natural_left C _ _ _ H K₁ K₂ L M f

/-- The explicit-owner internal-Hom tensor-source isomorphism is contravariantly natural in its
right tensor factor. -/
@[stacks 03EO "explicit internal-Hom tensor-source middle naturality"]
theorem isoOf_natural_middle
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K : C) {L₁ L₂ M : C} (f : L₁ ⟶ L₂) :
    (ihomOf H K).map ((preOf H f).app M) ≫ (isoOf H K L₁ M).hom =
      (isoOf H K L₂ M).hom ≫ (preOf H (K ◁ f)).app M :=
  @internalHomTensorIso_natural_middle C _ _ _ H K L₁ L₂ M f

/-- The explicit-owner internal-Hom tensor-source isomorphism is covariantly natural in its
target. -/
@[stacks 03EO "explicit internal-Hom tensor-source target naturality"]
theorem isoOf_natural_right
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (ihomOf H K).map ((ihomOf H L).map f) ≫ (isoOf H K L M₂).hom =
      (isoOf H K L M₁).hom ≫ (ihomOf H (K ⊗ L)).map f :=
  @internalHomTensorIso_natural_right C _ _ _ H K L M₁ M₂ f

/-- The inverse explicit-owner internal-Hom tensor-source isomorphism is contravariantly natural
in its left tensor factor. -/
@[reassoc, stacks 03EO "explicit inverse internal-Hom tensor-source left naturality"]
theorem isoOf_inv_natural_left
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L M : C} (f : K₁ ⟶ K₂) :
    (preOf H (f ▷ L)).app M ≫ (isoOf H K₁ L M).inv =
      (isoOf H K₂ L M).inv ≫
        (preOf H f).app ((ihomOf H L).obj M) := by
  symm
  apply (Iso.inv_comp_eq (isoOf H K₂ L M)).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv (isoOf H K₁ L M)).2
  exact isoOf_natural_left H f

/-- The inverse explicit-owner internal-Hom tensor-source isomorphism is contravariantly natural
in its right tensor factor. -/
@[reassoc, stacks 03EO "explicit inverse internal-Hom tensor-source middle naturality"]
theorem isoOf_inv_natural_middle
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K : C) {L₁ L₂ M : C} (f : L₁ ⟶ L₂) :
    (preOf H (K ◁ f)).app M ≫ (isoOf H K L₁ M).inv =
      (isoOf H K L₂ M).inv ≫
        (ihomOf H K).map ((preOf H f).app M) := by
  symm
  apply (Iso.inv_comp_eq (isoOf H K L₂ M)).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv (isoOf H K L₁ M)).2
  exact isoOf_natural_middle H K f

/-- The inverse explicit-owner internal-Hom tensor-source isomorphism is covariantly natural in
its target. -/
@[reassoc, stacks 03EO "explicit inverse internal-Hom tensor-source target naturality"]
theorem isoOf_inv_natural_right
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (ihomOf H (K ⊗ L)).map f ≫ (isoOf H K L M₂).inv =
      (isoOf H K L M₁).inv ≫
        (ihomOf H K).map ((ihomOf H L).map f) := by
  symm
  apply (Iso.inv_comp_eq (isoOf H K L M₁)).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv (isoOf H K L M₂)).2
  exact isoOf_natural_right H K L f

end InternalHomTensor

namespace TensorInternalHom

/-- The tensor of two explicit-owner internal-Hom morphisms. -/
@[stacks 0FXP "tensor of explicit-owner internal-Hom morphisms"]
noncomputable def tensorHomComparisonOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K K' M M' : C) :
    (ihomOf H K).obj K' ⊗ (ihomOf H M).obj M' ⟶
      (ihomOf H (K ⊗ M)).obj (K' ⊗ M') :=
  TensorInternalHom.comparisonOf H ((ihomOf H K).obj K') M' M ≫
    (ihomOf H M).map
      ((β_ ((ihomOf H K).obj K') M').hom ≫
        TensorInternalHom.comparisonOf H M' K' K ≫
          (ihomOf H K).map (β_ M' K').hom) ≫
    (InternalHomTensor.isoOf H M K (K' ⊗ M')).hom ≫
    (preOf H ((β_ K M).hom)).app (K' ⊗ M')

/-- The explicit-owner tensor-of-internal-Homs map is characterized by its four-stage
comparison, braiding, currying, and source transport composite. -/
@[stacks 0FXP "tensor of explicit-owner internal-Hom morphisms specification"]
theorem tensorHomComparisonOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K K' M M' : C) :
    tensorHomComparisonOf H K K' M M' =
      TensorInternalHom.comparisonOf H ((ihomOf H K).obj K') M' M ≫
        (ihomOf H M).map
          ((β_ ((ihomOf H K).obj K') M').hom ≫
            TensorInternalHom.comparisonOf H M' K' K ≫
              (ihomOf H K).map (β_ M' K').hom) ≫
        (InternalHomTensor.isoOf H M K (K' ⊗ M')).hom ≫
        (preOf H ((β_ K M).hom)).app (K' ⊗ M') :=
  @tensorHomComparison_spec C _ _ _ H K K' M M'

/-- The explicit-owner tensor-of-internal-Homs map is contravariantly natural in its first
internal-Hom source. -/
@[stacks 0FXP "explicit tensor-of-internal-Homs first-source naturality"]
theorem tensorHomComparisonOf_natural_leftSource
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K' M M' : C} (f : K₁ ⟶ K₂) :
    CommSq
      ((preOf H f).app K' ⊗ₘ 𝟙 ((ihomOf H M).obj M'))
      (tensorHomComparisonOf H K₂ K' M M')
      (tensorHomComparisonOf H K₁ K' M M')
      ((preOf H (f ⊗ₘ 𝟙 M)).app (K' ⊗ M')) :=
  @tensorHomComparison_natural_leftSource C _ _ _ H K₁ K₂ K' M M' f

/-- The explicit-owner tensor-of-internal-Homs map is covariantly natural in its first
internal-Hom target. -/
@[stacks 0FXP "explicit tensor-of-internal-Homs first-target naturality"]
theorem tensorHomComparisonOf_natural_leftTarget
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K M M' : C) {K₁' K₂' : C} (f : K₁' ⟶ K₂') :
    CommSq
      ((ihomOf H K).map f ⊗ₘ 𝟙 ((ihomOf H M).obj M'))
      (tensorHomComparisonOf H K K₁' M M')
      (tensorHomComparisonOf H K K₂' M M')
      ((ihomOf H (K ⊗ M)).map (f ⊗ₘ 𝟙 M')) :=
  @tensorHomComparison_natural_leftTarget C _ _ _ H K M M' K₁' K₂' f

/-- The explicit-owner tensor-of-internal-Homs map is contravariantly natural in its second
internal-Hom source. -/
@[stacks 0FXP "explicit tensor-of-internal-Homs second-source naturality"]
theorem tensorHomComparisonOf_natural_rightSource
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K K' M' : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    CommSq
      (𝟙 ((ihomOf H K).obj K') ⊗ₘ (preOf H f).app M')
      (tensorHomComparisonOf H K K' M₂ M')
      (tensorHomComparisonOf H K K' M₁ M')
      ((preOf H (𝟙 K ⊗ₘ f)).app (K' ⊗ M')) :=
  @tensorHomComparison_natural_rightSource C _ _ _ H K K' M' M₁ M₂ f

/-- The explicit-owner tensor-of-internal-Homs map is covariantly natural in its second
internal-Hom target. -/
@[stacks 0FXP "explicit tensor-of-internal-Homs second-target naturality"]
theorem tensorHomComparisonOf_natural_rightTarget
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K K' M : C) {M₁' M₂' : C} (f : M₁' ⟶ M₂') :
    CommSq
      (𝟙 ((ihomOf H K).obj K') ⊗ₘ (ihomOf H M).map f)
      (tensorHomComparisonOf H K K' M M₁')
      (tensorHomComparisonOf H K K' M M₂')
      ((ihomOf H (K ⊗ M)).map (𝟙 K' ⊗ₘ f)) :=
  @tensorHomComparison_natural_rightTarget C _ _ _ H K K' M M₁' M₂' f

end TensorInternalHom

namespace TensorRight

/-- The source-order tensor-to-iterated internal-Hom comparison
selected by an explicit closed owner.  This is the instance-free bridge to `Source.Iterated.map`. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92 "explicit tensor-to-iterated internal-Hom comparison"]
noncomputable abbrev comparisonOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (ihomOf H L).obj M ⊗ K ⟶ (ihomOf H ((ihomOf H K).obj L)).obj M :=
  @Source.Iterated.map C _ _ _ H K L M

/-- The tensor-side transpose defining the explicit-owner tensor-to-iterated-internal-Hom
comparison. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92
  "explicit tensor-to-iterated internal-Hom comparison transpose"]
noncomputable abbrev transposeOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (((ihomOf H L).obj M ⊗ K) ⊗ (ihomOf H K).obj L) ⟶ M :=
  @Source.Iterated.side C _ _ _ H K L M

/-- Source-order uncurrying of `comparisonOf` recovers its named tensor-side transpose. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92
  "explicit tensor-to-iterated internal-Hom transpose characterization"]
theorem comparisonOf_transpose
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    (braidedHomEquivOf H ((ihomOf H L).obj M ⊗ K)
        ((ihomOf H K).obj L) M).symm (comparisonOf H K L M) =
      transposeOf H K L M :=
  @Source.Iterated.map_spec C _ _ _ H K L M

/-- The explicit tensor-to-iterated internal-Hom comparison is the source-order canonical map. -/
@[stacks 0A8U "explicit tensor-to-iterated comparison specification"]
theorem comparisonOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    comparisonOf H K L M = @Source.Iterated.map C _ _ _ H K L M := rfl

/-- The explicit-owner tensor-to-iterated comparison uncurries to its evaluation composite. -/
@[stacks 0A67, stacks 0A92 "explicit tensor-to-iterated comparison uncurrying specification"]
theorem comparisonOf_uncurry
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L M : C) :
    uncurry (comparisonOf H K L M) =
      (α_ ((ihomOf H K).obj L) ((ihomOf H L).obj M) K).inv ≫
        ((β_ ((ihomOf H K).obj L) ((ihomOf H L).obj M)).hom ▷ K) ≫
          Source.compOf H K L M ▷ K ≫
            (β_ ((ihomOf H K).obj M) K).hom ≫
              uncurry (𝟙 ((ihomOf H K).obj M)) :=
  @Source.Iterated.map_uncurry C _ _ _ H K L M

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor-to-iterated internal-Hom comparison is natural in its tensor factor. -/
@[stacks 0A8U "explicit tensor-to-iterated tensor naturality"]
theorem comparisonOf_natural_tensor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L M : C} (fK : K₁ ⟶ K₂) :
    CommSq
      (𝟙 ((ihomOf H L).obj M) ⊗ₘ fK)
      (comparisonOf H K₁ L M)
      (comparisonOf H K₂ L M)
      ((preOf H ((preOf H fK).app L)).app M) := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  refine ⟨?_⟩
  have hbraidM :
      (β_ ((ihom K₂).obj M) K₁).hom ≫ K₁ ◁ (pre fK).app M =
        (pre fK).app M ▷ K₁ ≫ (β_ ((ihom K₁).obj M) K₁).hom :=
    (BraidedCategory.braiding_naturality_left ((pre fK).app M) K₁).symm
  have hcomp :
      Source.comp K₂ L M ▷ K₁ ≫ (pre fK).app M ▷ K₁ =
        (𝟙 ((ihom L).obj M) ⊗ₘ (pre fK).app L) ▷ K₁ ≫
          Source.comp K₁ L M ▷ K₁ := by
    simpa only [comp_whiskerRight] using
      congrArg (fun t => t ▷ K₁) (Source.comp_natural_source_assoc fK).symm
  have hbraidL :
      (β_ ((ihom K₂).obj L) ((ihom L).obj M)).hom ▷ K₁ ≫
          (𝟙 ((ihom L).obj M) ⊗ₘ (pre fK).app L) ▷ K₁ =
        ((pre fK).app L ⊗ₘ 𝟙 ((ihom L).obj M)) ▷ K₁ ≫
          (β_ ((ihom K₁).obj L) ((ihom L).obj M)).hom ▷ K₁ := by
    simpa only [id_tensorHom, tensorHom_id, comp_whiskerRight] using
      congrArg (fun t => t ▷ K₁)
        (BraidedCategory.braiding_naturality_left ((pre fK).app L)
          ((ihom L).obj M)).symm
  have hassoc :
      (α_ ((ihom K₂).obj L) ((ihom L).obj M) K₁).inv ≫
          ((pre fK).app L ⊗ₘ 𝟙 ((ihom L).obj M)) ▷ K₁ =
        (pre fK).app L ▷ ((ihom L).obj M ⊗ K₁) ≫
          (α_ ((ihom K₁).obj L) ((ihom L).obj M) K₁).inv := by
    simpa only [tensorHom_id] using
      (associator_inv_naturality_left ((pre fK).app L)
        ((ihom L).obj M) K₁).symm
  change (𝟙 ((ihom L).obj M) ⊗ₘ fK) ≫ Source.Iterated.map K₂ L M =
    Source.Iterated.map K₁ L M ≫ (pre ((pre fK).app L)).app M
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  rw [Source.Iterated.map_uncurry, Source.Iterated.map_uncurry]
  simp only [id_tensorHom, uncurry_id_eq_ev]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc,
    BraidedCategory.braiding_naturality_right_assoc,
    ← id_tensor_pre_app_comp_ev]
  slice_lhs 4 5 => rw [hbraidM]
  slice_lhs 3 4 => rw [hcomp]
  slice_lhs 2 3 => rw [hbraidL]
  slice_lhs 1 2 => rw [hassoc]
  simp only [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor-to-iterated internal-Hom comparison is contravariantly natural in its middle
factor. -/
@[stacks 0A8U "explicit tensor-to-iterated middle naturality"]
theorem comparisonOf_natural_middle
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K : C) {L₁ L₂ M : C} (fL : L₁ ⟶ L₂) :
    CommSq
      ((preOf H fL).app M ⊗ₘ 𝟙 K)
      (comparisonOf H K L₂ M)
      (comparisonOf H K L₁ M)
      ((preOf H ((ihomOf H K).map fL)).app M) := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  refine ⟨?_⟩
  have hcomp :
      (((pre fL).app M ▷ (ihom K).obj L₁) ▷ K) ≫
          Source.comp K L₁ M ▷ K =
        (𝟙 ((ihom L₂).obj M) ⊗ₘ (ihom K).map fL) ▷ K ≫
          Source.comp K L₂ M ▷ K := by
    simpa only [tensorHom_id, id_tensorHom, comp_whiskerRight] using
      congrArg (fun t => t ▷ K) (Source.comp_natural_middle K fL)
  have hbraid :
      (β_ ((ihom K).obj L₁) ((ihom L₂).obj M)).hom ▷ K ≫
          (𝟙 ((ihom L₂).obj M) ⊗ₘ (ihom K).map fL) ▷ K =
        ((ihom K).map fL ⊗ₘ 𝟙 ((ihom L₂).obj M)) ▷ K ≫
          (β_ ((ihom K).obj L₂) ((ihom L₂).obj M)).hom ▷ K := by
    simpa only [id_tensorHom, tensorHom_id, comp_whiskerRight] using
      congrArg (fun t => t ▷ K)
        (BraidedCategory.braiding_naturality_left ((ihom K).map fL)
          ((ihom L₂).obj M)).symm
  have hassoc :
      (α_ ((ihom K).obj L₁) ((ihom L₂).obj M) K).inv ≫
          ((ihom K).map fL ⊗ₘ 𝟙 ((ihom L₂).obj M)) ▷ K =
        (ihom K).map fL ▷ ((ihom L₂).obj M ⊗ K) ≫
          (α_ ((ihom K).obj L₂) ((ihom L₂).obj M) K).inv := by
    simpa only [tensorHom_id] using
      (associator_inv_naturality_left ((ihom K).map fL)
        ((ihom L₂).obj M) K).symm
  change ((pre fL).app M ⊗ₘ 𝟙 K) ≫ Source.Iterated.map K L₁ M =
    Source.Iterated.map K L₂ M ≫ (pre ((ihom K).map fL)).app M
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app]
  rw [Source.Iterated.map_uncurry, Source.Iterated.map_uncurry]
  simp only [tensorHom_id, uncurry_id_eq_ev]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc]
  slice_lhs 3 4 => rw [hcomp]
  slice_lhs 2 3 => rw [hbraid]
  slice_lhs 1 2 => rw [hassoc]
  simp only [Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor-to-iterated internal-Hom comparison is natural in its target. -/
@[stacks 0A8U "explicit tensor-to-iterated target naturality"]
theorem comparisonOf_natural_target
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (K L : C) {M₁ M₂ : C} (fM : M₁ ⟶ M₂) :
    CommSq
      (((ihomOf H L).map fM) ⊗ₘ 𝟙 K)
      (comparisonOf H K L M₁)
      (comparisonOf H K L M₂)
      ((ihomOf H ((ihomOf H K).obj L)).map fM) := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  refine ⟨?_⟩
  have hcomp :
      (((ihom L).map fM ▷ (ihom K).obj L) ▷ K) ≫
          Source.comp K L M₂ ▷ K =
        Source.comp K L M₁ ▷ K ≫ (ihom K).map fM ▷ K := by
    simpa only [tensorHom_id, comp_whiskerRight] using
      congrArg (fun t => t ▷ K) (Source.comp_natural_target_assoc K L fM)
  change (((ihom L).map fM ⊗ₘ 𝟙 K) ≫ Source.Iterated.map K L M₂ =
    Source.Iterated.map K L M₁ ≫ (ihom ((ihom K).obj L)).map fM)
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  rw [Source.Iterated.map_uncurry, Source.Iterated.map_uncurry]
  simp only [tensorHom_id, uncurry_id_eq_ev]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc]
  slice_lhs 3 4 =>
    rw [hcomp]
  have hbraid :
      (ihom K).map fM ▷ K ≫ (β_ ((ihom K).obj M₂) K).hom =
        (β_ ((ihom K).obj M₁) K).hom ≫ K ◁ (ihom K).map fM :=
    BraidedCategory.braiding_naturality_left ((ihom K).map fM) K
  have hev :
      K ◁ (ihom K).map fM ≫ (ihom.ev K).app M₂ =
        (ihom.ev K).app M₁ ≫ fM := by
    change (ihom K ⋙ tensorLeft K).map fM ≫ (ihom.ev K).app M₂ =
      (ihom.ev K).app M₁ ≫ (𝟭 C).map fM
    exact (ihom.ev K).naturality fM
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [hbraid]
  slice_lhs 5 6 => rw [hev]

end TensorRight

end CategoryTheory.MonoidalClosed
