/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.ExplicitCore
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.UnitEndPairing
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.BraidedComparisons
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality.LeftAdjointMate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-variable internal-Hom functoriality and the full functoriality API
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory
noncomputable section
universe v u
namespace CategoryTheory.MonoidalClosed

/-- The two-variable internal-Hom map selected by an explicit closed-monoidal owner. -/
noncomputable def internalHomMapOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    (ihomOf H K₁).obj L₁ ⟶ (ihomOf H K₂).obj L₂ :=
  (preOf H fK).app L₁ ≫ (ihomOf H K₂).map fL

/-- The explicit-owner two-variable map is the map of the uncurried selected internal-Hom
bifunctor on the product morphism `(fK.op, fL)`. -/
theorem internalHomMapOf_uncurry_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    internalHomMapOf H fK fL =
      (Functor.uncurry.obj (internalHomOf H)).map
        ((fK.op, fL) :
          (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)) := rfl

namespace Source

/-- The source-order two-variable internal-Hom map selected by an explicit closed owner.
It is the source-facing view of `internalHomMapOf`, with the target-variable map written first. -/
@[stacks 0A95 "explicit source-order internal-Hom map"]
noncomputable abbrev mapOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L' L I' I : C}
    (f : L' ⟶ L) (g : I' ⟶ I) :
    (ihomOf H L).obj I' ⟶ (ihomOf H L').obj I :=
  internalHomMapOf H f g

/-- The source-order map expands to postcomposition followed by precomposition. -/
@[stacks 0A95 "explicit source-order internal-Hom map specification"]
theorem mapOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L' L I' I : C}
    (f : L' ⟶ L) (g : I' ⟶ I) :
    mapOf H f g = (ihomOf H L).map g ≫ (preOf H f).app I :=
  preOf_naturality H f g

/-- Identity maps induce the identity source-order internal-Hom map. -/
@[simp]
theorem mapOf_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (L I : C) :
    mapOf H (𝟙 L) (𝟙 I) = 𝟙 _ := by
  rw [mapOf_spec, Functor.map_id, preOf_id_app, Category.id_comp]
  rfl

/-- Source-order internal-Hom maps compose contravariantly in their source and covariantly in
their target. -/
@[reassoc]
theorem mapOf_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ L₃ I₁ I₂ I₃ : C}
    (f₁ : L₂ ⟶ L₁) (f₂ : L₃ ⟶ L₂)
    (g₁ : I₁ ⟶ I₂) (g₂ : I₂ ⟶ I₃) :
    mapOf H (f₂ ≫ f₁) (g₁ ≫ g₂) =
      mapOf H f₁ g₁ ≫ mapOf H f₂ g₂ := by
  simpa only [mapOf, internalHomMapOf, preOf_comp_app, Functor.map_comp,
      Category.assoc] using
    congrArg
      (fun t ↦ (preOf H f₁).app I₁ ≫ t ≫ (ihomOf H L₃).map g₂)
      (preOf_naturality H f₂ g₁)

/-- The source-order map with an identity target map is the selected precomposition component. -/
@[simp]
theorem mapOf_pre
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L' L I : C} (f : L' ⟶ L) :
    mapOf H f (𝟙 I) = (preOf H f).app I := by
  simp [mapOf, internalHomMapOf]

/-- The source-order map with an identity source map is the selected postcomposition map. -/
@[simp]
theorem mapOf_post
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L I' I : C} (g : I' ⟶ I) :
    mapOf H (𝟙 L) g = (ihomOf H L).map g := by
  rw [mapOf, internalHomMapOf, preOf_id_app]
  exact Category.id_comp _

/-- The source-order map is the uncurried selected internal-Hom bifunctor map on `(f.op, g)`. -/
theorem mapOf_uncurry_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L' L I' I : C}
    (f : L' ⟶ L) (g : I' ⟶ I) :
    mapOf H f g =
      (Functor.uncurry.obj (internalHomOf H)).map
        ((f.op, g) :
          (Opposite.op L, I') ⟶ (Opposite.op L', I)) :=
  internalHomMapOf_uncurry_map H f g

end Source

/-- `internalHomMapOf` restricts to precomposition when the target-variable map is the identity. -/
@[simp]
theorem internalHomMapOf_pre
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L : C} (fK : K₂ ⟶ K₁) :
    internalHomMapOf H fK (𝟙 L) = (preOf H fK).app L := by
  simp [internalHomMapOf]

/-- `internalHomMapOf` restricts to postcomposition when the source-variable map is the identity. -/
@[simp]
theorem internalHomMapOf_post
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K L₁ L₂ : C} (fL : L₁ ⟶ L₂) :
    internalHomMapOf H (𝟙 K) fL = (ihomOf H K).map fL := by
  rw [internalHomMapOf, preOf_id_app]
  exact Category.id_comp _

/-- The explicit-owner internal-Hom map induced by identity morphisms is the identity. -/
@[simp]
theorem internalHomMapOf_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L : C) :
    internalHomMapOf H (𝟙 K) (𝟙 L) = 𝟙 _ := by
  rw [internalHomMapOf_post, Functor.map_id]

/-- Explicit-owner internal-Hom maps compose contravariantly in their source variables and
covariantly in their target variables. -/
@[reassoc]
theorem internalHomMapOf_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K₃ L₁ L₂ L₃ : C}
    (fK₁ : K₂ ⟶ K₁) (fK₂ : K₃ ⟶ K₂)
    (fL₁ : L₁ ⟶ L₂) (fL₂ : L₂ ⟶ L₃) :
    internalHomMapOf H (fK₂ ≫ fK₁) (fL₁ ≫ fL₂) =
      internalHomMapOf H fK₁ fL₁ ≫ internalHomMapOf H fK₂ fL₂ := by
  simpa only [internalHomMapOf, preOf_comp_app, Functor.map_comp, Category.assoc] using
    congrArg
      (fun t ↦ (preOf H fK₁).app L₁ ≫ t ≫ (ihomOf H K₃).map fL₂)
      (preOf_naturality H fK₂ fL₁)

/-- Explicit-owner composition is simultaneously natural in its source, middle, and target;
the mixed source records the opposite variance of the middle internal Hom. -/
@[stacks 0A8J "explicit closed-owner composition simultaneous naturality"]
theorem compOf_natural
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (internalHomMapOf H fK fL ⊗ₘ internalHomMapOf H (𝟙 L₂) fM)
      (𝟙 ((ihomOf H K₁).obj L₁) ⊗ₘ internalHomMapOf H fL (𝟙 M₁))
      (compOf H K₂ L₂ M₂)
      (compOf H K₁ L₁ M₁ ≫ internalHomMapOf H fK fM) := by
  refine ⟨?_⟩
  simp only [internalHomMapOf_pre, internalHomMapOf_post]
  calc
    (internalHomMapOf H fK fL ⊗ₘ (ihomOf H L₂).map fM) ≫
        compOf H K₂ L₂ M₂ =
      (internalHomMapOf H fK fL ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
        (𝟙 ((ihomOf H K₂).obj L₂) ⊗ₘ (ihomOf H L₂).map fM) ≫
          compOf H K₂ L₂ M₂ := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
              Category.comp_id, Category.id_comp]
    _ = (internalHomMapOf H fK fL ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
        compOf H K₂ L₂ M₁ ≫ (ihomOf H K₂).map fM := by
          rw [compOf_natural_target H K₂ L₂ fM]
    _ = ((preOf H fK).app L₁ ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
        ((ihomOf H K₂).map fL ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
          compOf H K₂ L₂ M₁ ≫ (ihomOf H K₂).map fM := by
            rw [internalHomMapOf]
            rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
              Category.comp_id]
    _ = ((ihomOf H K₁).map fL ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
        ((preOf H fK).app L₂ ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
          compOf H K₂ L₂ M₁ ≫ (ihomOf H K₂).map fM := by
            rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
              MonoidalCategory.tensorHom_comp_tensorHom_assoc,
              Category.comp_id, preOf_naturality H fK fL]
    _ = ((ihomOf H K₁).map fL ⊗ₘ 𝟙 ((ihomOf H L₂).obj M₁)) ≫
        compOf H K₁ L₂ M₁ ≫ (preOf H fK).app M₁ ≫
          (ihomOf H K₂).map fM := by
            rw [compOf_natural_source_assoc H fK]
    _ = (𝟙 ((ihomOf H K₁).obj L₁) ⊗ₘ (preOf H fL).app M₁) ≫
        compOf H K₁ L₁ M₁ ≫ (preOf H fK).app M₁ ≫
          (ihomOf H K₂).map fM := by
            rw [← compOf_natural_middle_assoc H K₁ fL]
    _ = (𝟙 ((ihomOf H K₁).obj L₁) ⊗ₘ (preOf H fL).app M₁) ≫
        compOf H K₁ L₁ M₁ ≫ internalHomMapOf H fK fM := rfl

namespace Source

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Explicit source-order composition is simultaneously natural in its source, middle, and
target, with the mixed source exposing the middle variance. -/
@[stacks 0A8J, stacks 0A8V, stacks 0A91
  "explicit source-order composition simultaneous naturality"]
theorem compOf_natural
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (internalHomMapOf H (𝟙 L₂) fM ⊗ₘ internalHomMapOf H fK fL)
      (internalHomMapOf H fL (𝟙 M₁) ⊗ₘ 𝟙 ((ihomOf H K₁).obj L₁))
      (compOf H K₂ L₂ M₂)
      (compOf H K₁ L₁ M₁ ≫ internalHomMapOf H fK fM) := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  refine ⟨?_⟩
  rw [Source.compOf_spec, Source.compOf_spec]
  simp only [Category.assoc]
  calc
    (internalHomMapOf H (𝟙 L₂) fM ⊗ₘ internalHomMapOf H fK fL) ≫
        (β_ ((ihomOf H L₂).obj M₂) ((ihomOf H K₂).obj L₂)).hom ≫
          CategoryTheory.MonoidalClosed.compOf H K₂ L₂ M₂ =
      (β_ ((ihomOf H L₂).obj M₁) ((ihomOf H K₁).obj L₁)).hom ≫
        (internalHomMapOf H fK fL ⊗ₘ internalHomMapOf H (𝟙 L₂) fM) ≫
          CategoryTheory.MonoidalClosed.compOf H K₂ L₂ M₂ := by
            rw [BraidedCategory.braiding_naturality_assoc]
    _ = (β_ ((ihomOf H L₂).obj M₁) ((ihomOf H K₁).obj L₁)).hom ≫
        (𝟙 ((ihomOf H K₁).obj L₁) ⊗ₘ internalHomMapOf H fL (𝟙 M₁)) ≫
          CategoryTheory.MonoidalClosed.compOf H K₁ L₁ M₁ ≫
            internalHomMapOf H fK fM := by
            rw [(CategoryTheory.MonoidalClosed.compOf_natural H fK fL fM).w]
    _ = (internalHomMapOf H fL (𝟙 M₁) ⊗ₘ 𝟙 ((ihomOf H K₁).obj L₁)) ≫
        (β_ ((ihomOf H L₁).obj M₁) ((ihomOf H K₁).obj L₁)).hom ≫
          CategoryTheory.MonoidalClosed.compOf H K₁ L₁ M₁ ≫ internalHomMapOf H fK fM := by
            rw [← BraidedCategory.braiding_naturality_assoc]

end Source

namespace TensorRight

/-- Simultaneous naturality of the explicit-owner tensor-to-iterated-internal-Hom comparison in
its tensor factor, middle source, and final target. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92
  "explicit tensor-to-iterated internal-Hom simultaneous naturality"]
theorem comparisonOf_natural
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (internalHomMapOf H fL fM ⊗ₘ fK)
      (comparisonOf H K₁ L₂ M₁)
      (comparisonOf H K₂ L₁ M₂)
      (internalHomMapOf H (internalHomMapOf H fK fL) fM) := by
  refine ⟨?_⟩
  simp only [internalHomMapOf]
  calc
    (((preOf H fL).app M₁ ≫ (ihomOf H L₁).map fM) ⊗ₘ fK) ≫
        comparisonOf H K₂ L₁ M₂ =
      ((preOf H fL).app M₁ ⊗ₘ 𝟙 K₁) ≫
        ((ihomOf H L₁).map fM ⊗ₘ 𝟙 K₁) ≫
          (𝟙 ((ihomOf H L₁).obj M₂) ⊗ₘ fK) ≫
            comparisonOf H K₂ L₁ M₂ := by
              rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
                MonoidalCategory.tensorHom_comp_tensorHom_assoc]
              simp only [Category.comp_id, Category.id_comp]
    _ = ((preOf H fL).app M₁ ⊗ₘ 𝟙 K₁) ≫
        ((ihomOf H L₁).map fM ⊗ₘ 𝟙 K₁) ≫
          comparisonOf H K₁ L₁ M₂ ≫
            (preOf H ((preOf H fK).app L₁)).app M₂ := by
              slice_lhs 3 4 =>
                rw [(comparisonOf_natural_tensor H fK).w]
    _ = ((preOf H fL).app M₁ ⊗ₘ 𝟙 K₁) ≫
        comparisonOf H K₁ L₁ M₁ ≫
          (ihomOf H ((ihomOf H K₁).obj L₁)).map fM ≫
            (preOf H ((preOf H fK).app L₁)).app M₂ := by
              slice_lhs 2 3 =>
                rw [(comparisonOf_natural_target H K₁ L₁ fM).w]
              simp only [Category.assoc]
    _ = comparisonOf H K₁ L₂ M₁ ≫
        (preOf H ((ihomOf H K₁).map fL)).app M₁ ≫
          (ihomOf H ((ihomOf H K₁).obj L₁)).map fM ≫
            (preOf H ((preOf H fK).app L₁)).app M₂ := by
              slice_lhs 1 2 =>
                rw [(comparisonOf_natural_middle H K₁ fL).w]
              simp only [Category.assoc]
    _ = comparisonOf H K₁ L₂ M₁ ≫
        internalHomMapOf H (internalHomMapOf H fK fL) fM := by
          slice_lhs 3 4 =>
            rw [← preOf_naturality H ((preOf H fK).app L₁) fM]
          slice_lhs 2 3 =>
            rw [← NatTrans.comp_app, ← preOf_comp H]
          rfl

end TensorRight

/-- An explicit-owner internal-Hom map is an isomorphism when both variable maps are
isomorphisms. -/
instance isIso_internalHomMapOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) [IsIso fK] [IsIso fL] :
    IsIso (internalHomMapOf H fK fL) := by
  change IsIso ((Functor.uncurry.obj (internalHomOf H)).map
    ((fK.op, fL) :
      (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)))
  -- Local instance justification (proof-local temporary data): install the product-morphism
  -- `IsIso` fact only to derive the internal-Hom map isomorphism in this proof.
  letI : IsIso ((fK.op, fL) :
      (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)) :=
    (isIso_prod_iff (C := Cᵒᵖ) (D := C)).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- The explicit-owner internal-Hom maps induced by two isomorphisms and their inverses compose to
the identity on the source object. -/
theorem internalHomMapIsoOf_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMapOf H eK.hom eL.hom ≫ internalHomMapOf H eK.inv eL.inv = 𝟙 _ := by
  rw [← internalHomMapOf_comp, eK.inv_hom_id, eL.hom_inv_id,
    internalHomMapOf_id]

/-- The explicit-owner internal-Hom maps induced by the inverses of two isomorphisms and by the
isomorphisms compose to the identity on the target object. -/
theorem internalHomMapIsoOf_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMapOf H eK.inv eL.inv ≫ internalHomMapOf H eK.hom eL.hom = 𝟙 _ := by
  rw [← internalHomMapOf_comp, eK.hom_inv_id, eL.inv_hom_id,
    internalHomMapOf_id]

/-- The explicit-owner two-variable internal-Hom map packaged as an isomorphism. -/
noncomputable abbrev internalHomMapIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (ihomOf H K₁).obj L₁ ≅ (ihomOf H K₂).obj L₂ :=
  (Functor.uncurry.obj (internalHomOf H)).mapIso (Iso.prod eK.op eL)

/-- `internalHomMapIsoOf` is the image of the product isomorphism under the uncurried selected
internal-Hom bifunctor. -/
theorem internalHomMapIsoOf_uncurry_mapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMapIsoOf H eK eL =
      (Functor.uncurry.obj (internalHomOf H)).mapIso (Iso.prod eK.op eL) := rfl

/-- The forward map of `internalHomMapIsoOf` is the explicit-owner internal-Hom map. -/
@[simp]
theorem internalHomMapIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (internalHomMapIsoOf H eK eL).hom = internalHomMapOf H eK.hom eL.hom := rfl

/-- The inverse of `internalHomMapIsoOf` is the explicit-owner map on inverse morphisms. -/
@[simp]
theorem internalHomMapIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (internalHomMapIsoOf H eK eL).inv = internalHomMapOf H eK.inv eL.inv := rfl

/-- The explicit-owner internal-Hom isomorphism induced by identity maps is the identity. -/
@[simp]
theorem internalHomMapIsoOf_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L : C) :
    internalHomMapIsoOf H (Iso.refl K) (Iso.refl L) = Iso.refl _ := by
  apply Iso.ext
  change internalHomMapOf H (𝟙 K) (𝟙 L) = 𝟙 _
  exact internalHomMapOf_id H K L

/-- Explicit-owner internal-Hom isomorphisms compose in their two variables. -/
theorem internalHomMapIsoOf_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K₃ L₁ L₂ L₃ : C}
    (eK₁ : K₂ ≅ K₁) (eK₂ : K₃ ≅ K₂)
    (eL₁ : L₁ ≅ L₂) (eL₂ : L₂ ≅ L₃) :
    internalHomMapIsoOf H (eK₂ ≪≫ eK₁) (eL₁ ≪≫ eL₂) =
      internalHomMapIsoOf H eK₁ eL₁ ≪≫ internalHomMapIsoOf H eK₂ eL₂ := by
  apply Iso.ext
  exact internalHomMapOf_comp H eK₁.hom eK₂.hom eL₁.hom eL₂.hom

/-- The canonical fixed-target internal-Hom functor in the contravariant source variable. -/
@[stacks 0A65 "canonical source-variable internal-Hom functor"]
noncomputable abbrev sourceFunctor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (L : C) : Cᵒᵖ ⥤ C :=
  (Functor.flip (MonoidalClosed.internalHom)).obj L

/-- The object formula for the canonical source-variable internal-Hom functor. -/
@[simp]
theorem sourceFunctor_obj
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (L K : C) :
    (sourceFunctor L).obj (Opposite.op K) = (ihom K).obj L :=
  sourceFunctorOf_obj (inferInstance : MonoidalClosed C) L K

/-- The map formula for the canonical source-variable internal-Hom functor. -/
theorem sourceFunctor_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L : C} (f : K₂ ⟶ K₁) :
    (sourceFunctor L).map f.op = (pre f).app L :=
  sourceFunctorOf_map (inferInstance : MonoidalClosed C) f

/-- The canonical postcomposition natural transformation in the target variable. -/
@[stacks 0A65 "canonical postcomposition in the target variable"]
noncomputable abbrev post
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    sourceFunctor L₁ ⟶ sourceFunctor L₂ :=
  (Functor.flip (MonoidalClosed.internalHom)).map f

/-- Identity target maps induce the identity canonical source-variable transformation. -/
@[simp]
theorem post_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (L : C) :
    post (𝟙 L) = 𝟙 (sourceFunctor L) :=
  postOf_id (inferInstance : MonoidalClosed C) L

/-- Canonical postcomposition is covariantly functorial in the target variable. -/
theorem post_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ L₃ : C} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    post (f ≫ g) = post f ≫ post g :=
  postOf_comp (inferInstance : MonoidalClosed C) f g

/-- The component of canonical postcomposition is the internal-Hom target map. -/
@[simp]
theorem post_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) (K : C) :
    (post f).app (Opposite.op K) = (ihom K).map f :=
  postOf_app (inferInstance : MonoidalClosed C) f K

/-- Canonical postcomposition is natural in the contravariant source variable. -/
@[reassoc]
theorem post_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    (sourceFunctor L₁).map fK.op ≫
        (post fL).app (Opposite.op K₂) =
      (post fL).app (Opposite.op K₁) ≫
        (sourceFunctor L₂).map fK.op :=
  postOf_naturality (inferInstance : MonoidalClosed C) fK fL

/-- An isomorphism of canonical internal-Hom source objects induces the contravariant
isomorphism of their target-variable functors. -/
noncomputable abbrev preIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    ihom K₁ ≅ ihom K₂ :=
  preIsoOf (inferInstance : MonoidalClosed C) e

/-- The forward component of `preIso` is canonical precomposition by the inverse source
isomorphism. -/
@[simp]
theorem preIso_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (e : K₁ ≅ K₂) (L : C) :
    (preIso e).hom.app L = (pre e.inv).app L :=
  preIsoOf_hom_app (inferInstance : MonoidalClosed C) e L

/-- The inverse component of `preIso` is canonical precomposition by the forward source
isomorphism. -/
@[simp]
theorem preIso_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (e : K₁ ≅ K₂) (L : C) :
    (preIso e).inv.app L = (pre e.hom).app L :=
  preIsoOf_inv_app (inferInstance : MonoidalClosed C) e L

/-- The forward natural transformation of `preIso` is canonical precomposition by the inverse
source isomorphism. -/
@[simp]
theorem preIso_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    (preIso e).hom = pre e.inv :=
  preIsoOf_hom (inferInstance : MonoidalClosed C) e

/-- The inverse natural transformation of `preIso` is canonical precomposition by the forward
source isomorphism. -/
@[simp]
theorem preIso_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    (preIso e).inv = pre e.hom :=
  preIsoOf_inv (inferInstance : MonoidalClosed C) e

/-- The canonical target-variable isomorphism induced by an identity source is the identity. -/
@[simp]
theorem preIso_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (K : C) :
    preIso (Iso.refl K) = Iso.refl _ :=
  preIsoOf_refl (inferInstance : MonoidalClosed C) K

/-- Canonical target-variable isomorphisms compose contravariantly in the source parameter. -/
theorem preIso_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ K₃ : C} (e₁ : K₁ ≅ K₂) (e₂ : K₂ ≅ K₃) :
    preIso (e₁ ≪≫ e₂) = preIso e₁ ≪≫ preIso e₂ :=
  preIsoOf_trans (inferInstance : MonoidalClosed C) e₁ e₂

/-- An isomorphism of canonical internal-Hom target objects induces the covariant isomorphism of
their source-variable functors. -/
noncomputable abbrev postIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    sourceFunctor L₁ ≅ sourceFunctor L₂ :=
  postIsoOf (inferInstance : MonoidalClosed C) e

/-- The forward component of `postIso` is canonical postcomposition by the forward target
isomorphism. -/
@[simp]
theorem postIso_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (e : L₁ ≅ L₂) (K : C) :
    (postIso e).hom.app (Opposite.op K) = (ihom K).map e.hom :=
  postIsoOf_hom_app (inferInstance : MonoidalClosed C) e K

/-- The inverse component of `postIso` is canonical postcomposition by the inverse target
isomorphism. -/
@[simp]
theorem postIso_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (e : L₁ ≅ L₂) (K : C) :
    (postIso e).inv.app (Opposite.op K) = (ihom K).map e.inv :=
  postIsoOf_inv_app (inferInstance : MonoidalClosed C) e K

/-- The forward natural transformation of `postIso` is canonical postcomposition by the forward
target isomorphism. -/
@[simp]
theorem postIso_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (postIso e).hom = post e.hom :=
  postIsoOf_hom (inferInstance : MonoidalClosed C) e

/-- The inverse natural transformation of `postIso` is canonical postcomposition by the inverse
target isomorphism. -/
@[simp]
theorem postIso_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (postIso e).inv = post e.inv :=
  postIsoOf_inv (inferInstance : MonoidalClosed C) e

/-- The canonical source-variable isomorphism induced by an identity target is the identity. -/
@[simp]
theorem postIso_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (L : C) :
    postIso (Iso.refl L) = Iso.refl _ :=
  postIsoOf_refl (inferInstance : MonoidalClosed C) L

/-- Canonical source-variable isomorphisms compose in the target parameter. -/
theorem postIso_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ L₃ : C} (e₁ : L₁ ≅ L₂) (e₂ : L₂ ≅ L₃) :
    postIso (e₁ ≪≫ e₂) = postIso e₁ ≪≫ postIso e₂ :=
  postIsoOf_trans (inferInstance : MonoidalClosed C) e₁ e₂

/-- Canonical precomposition is contravariantly functorial in its internal-Hom source parameter.
This names the composition law beside the inferred two-variable map API. -/
theorem pre_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ K₃ : C} (f : K₂ ⟶ K₁) (g : K₃ ⟶ K₂) :
    pre (g ≫ f) = pre f ≫ pre g :=
  preOf_comp (inferInstance : MonoidalClosed C) f g

/-- Canonical precomposition commutes with morphisms in the internal-Hom target variable. -/
@[reassoc]
theorem pre_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂) :
    (pre f).app L₁ ≫ (ihom K₂).map g =
      (ihom K₁).map g ≫ (pre f).app L₂ :=
  preOf_naturality (inferInstance : MonoidalClosed C) f g

/-- The map on internal-Hom objects induced contravariantly in the source and covariantly in the
target. -/
noncomputable def internalHomMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    (ihom K₁).obj L₁ ⟶ (ihom K₂).obj L₂ :=
  internalHomMapOf (inferInstance : MonoidalClosed C) fK fL

/-- The canonical two-variable internal-Hom map is the map of the uncurried internal-Hom
bifunctor on the product morphism `(fK.op, fL)`. -/
theorem internalHomMap_uncurry_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    internalHomMap fK fL =
      (Functor.uncurry.obj MonoidalClosed.internalHom).map
        ((fK.op, fL) :
          (Opposite.op K₁, L₁) ⟶ (Opposite.op K₂, L₂)) :=
  internalHomMapOf_uncurry_map (inferInstance : MonoidalClosed C) fK fL

/-- The component of canonical precomposition is the corresponding two-variable internal-Hom map. -/
theorem pre_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ : C} (fK : K₂ ⟶ K₁) (L : C) :
    (pre fK).app L = internalHomMap fK (𝟙 L) :=
  (internalHomMapOf_pre (inferInstance : MonoidalClosed C) fK).symm

/-- `internalHomMap` restricts to precomposition when its target-variable map is the identity. -/
@[simp]
theorem internalHomMap_pre
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L : C} (fK : K₂ ⟶ K₁) :
    internalHomMap fK (𝟙 L) = (pre fK).app L :=
  internalHomMapOf_pre (inferInstance : MonoidalClosed C) fK

/-- `internalHomMap` restricts to postcomposition when its source-variable map is the identity. -/
@[simp]
theorem internalHomMap_post
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K L₁ L₂ : C} (fL : L₁ ⟶ L₂) :
    internalHomMap (𝟙 K) fL = (ihom K).map fL :=
  internalHomMapOf_post (inferInstance : MonoidalClosed C) fL

/-- The internal-Hom map induced by identity morphisms is the identity. -/
@[simp]
theorem internalHomMap_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (K L : C) :
    internalHomMap (𝟙 K) (𝟙 L) = 𝟙 _ :=
  internalHomMapOf_id (inferInstance : MonoidalClosed C) K L

/-- Internal-Hom maps compose contravariantly in their source variables and covariantly in their
target variables. -/
@[reassoc]
theorem internalHomMap_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ K₃ L₁ L₂ L₃ : C}
    (fK₁ : K₂ ⟶ K₁) (fK₂ : K₃ ⟶ K₂)
    (fL₁ : L₁ ⟶ L₂) (fL₂ : L₂ ⟶ L₃) :
    internalHomMap (fK₂ ≫ fK₁) (fL₁ ≫ fL₂) =
      internalHomMap fK₁ fL₁ ≫ internalHomMap fK₂ fL₂ :=
  internalHomMapOf_comp (inferInstance : MonoidalClosed C) fK₁ fK₂ fL₁ fL₂

/-- Canonical closed composition is simultaneously natural in its source, middle, and
target; the mixed source records the opposite variance of the middle internal Hom. -/
@[stacks 0A8J "canonical closed composition simultaneous naturality"]
theorem comp_natural
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ M₁ M₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (internalHomMap fK fL ⊗ₘ internalHomMap (𝟙 L₂) fM)
      (𝟙 ((ihom K₁).obj L₁) ⊗ₘ internalHomMap fL (𝟙 M₁))
      (comp K₂ L₂ M₂)
      (comp K₁ L₁ M₁ ≫ internalHomMap fK fM) :=
  compOf_natural (inferInstance : MonoidalClosed C) fK fL fM

/-- Canonical closed composition is covariantly natural in its final target. -/
@[reassoc]
theorem comp_natural_target
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (𝟙 ((ihom K).obj L) ⊗ₘ (ihom L).map f) ≫ comp K L M₂ =
      comp K L M₁ ≫ (ihom K).map f :=
  compOf_natural_target (inferInstance : MonoidalClosed C) K L f

/-- Canonical closed composition is contravariantly natural in its first internal-Hom source. -/
@[reassoc]
theorem comp_natural_source
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K K' L M : C} (f : K ⟶ K') :
    ((pre f).app L ⊗ₘ 𝟙 ((ihom L).obj M)) ≫ comp K L M =
      comp K' L M ≫ (pre f).app M :=
  compOf_natural_source (inferInstance : MonoidalClosed C) f

/-- Canonical closed composition has opposite variance in its middle internal-Hom parameter. -/
@[reassoc]
theorem comp_natural_middle
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (K : C) {L L' M : C} (g : L ⟶ L') :
    (𝟙 ((ihom K).obj L) ⊗ₘ (pre g).app M) ≫ comp K L M =
      ((ihom K).map g ⊗ₘ 𝟙 ((ihom L').obj M)) ≫ comp K L' M :=
  compOf_natural_middle (inferInstance : MonoidalClosed C) K g

namespace Source

/-- The source-order canonical internal-Hom map agrees with `internalHomMap`. -/
theorem map_eq_internalHomMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L' L I' I : C} (f : L' ⟶ L) (g : I' ⟶ I) :
    map f g = internalHomMap f g :=
  (mapOf_spec (inferInstance : MonoidalClosed C) f g).symm

/-- Identity maps induce the identity source-order canonical internal-Hom map. -/
@[simp]
theorem map_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (L I : C) :
    map (𝟙 L) (𝟙 I) = 𝟙 _ := by
  rw [map_eq_internalHomMap, internalHomMap_id]

/-- Source-order canonical internal-Hom maps compose contravariantly in their source and
covariantly in their target. -/
@[reassoc]
theorem map_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L₁ L₂ L₃ I₁ I₂ I₃ : C}
    (f₁ : L₂ ⟶ L₁) (f₂ : L₃ ⟶ L₂)
    (g₁ : I₁ ⟶ I₂) (g₂ : I₂ ⟶ I₃) :
    map (f₂ ≫ f₁) (g₁ ≫ g₂) =
      map f₁ g₁ ≫ map f₂ g₂ := by
  simpa only [map_eq_internalHomMap] using
    internalHomMap_comp f₁ f₂ g₁ g₂

/-- The source-order canonical map with an identity target map is precomposition. -/
@[simp]
theorem map_pre
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L' L I : C} (f : L' ⟶ L) :
    map f (𝟙 I) = (pre f).app I := by
  rw [map_eq_internalHomMap, internalHomMap_pre]

/-- The source-order canonical map with an identity source map is postcomposition. -/
@[simp]
theorem map_post
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L I' I : C} (g : I' ⟶ I) :
    map (𝟙 L) g = (ihom L).map g := by
  rw [map_eq_internalHomMap, internalHomMap_post]

/-- The source-order canonical map is the uncurried internal-Hom bifunctor map on
`(f.op, g)`. -/
theorem map_uncurry_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {L' L I' I : C} (f : L' ⟶ L) (g : I' ⟶ I) :
    map f g =
      (Functor.uncurry.obj MonoidalClosed.internalHom).map
        ((f.op, g) :
          (Opposite.op L, I') ⟶ (Opposite.op L', I)) := by
  rw [map_eq_internalHomMap]
  exact internalHomMap_uncurry_map f g

end Source

/-- An internal-Hom map is an isomorphism when both of its source and target variable maps are
isomorphisms. -/
instance isIso_internalHomMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂)
    [IsIso fK] [IsIso fL] :
    IsIso (internalHomMap fK fL) :=
  isIso_internalHomMapOf (inferInstance : MonoidalClosed C) fK fL

/-- Composing the internal-Hom maps induced by a pair of isomorphisms and their inverses gives the
identity on the source internal-Hom object. -/
theorem internalHomMapIso_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMap eK.hom eL.hom ≫ internalHomMap eK.inv eL.inv = 𝟙 _ :=
  internalHomMapIsoOf_hom_inv_id (inferInstance : MonoidalClosed C) eK eL

/-- Composing the internal-Hom maps induced by the inverses of two isomorphisms and by the original
isomorphisms gives the identity on the target internal-Hom object. -/
theorem internalHomMapIso_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMap eK.inv eL.inv ≫ internalHomMap eK.hom eL.hom = 𝟙 _ :=
  internalHomMapIsoOf_inv_hom_id (inferInstance : MonoidalClosed C) eK eL

/-- The two-variable internal-Hom map packaged as an isomorphism. -/
noncomputable def internalHomMapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (ihom K₁).obj L₁ ≅ (ihom K₂).obj L₂ :=
  internalHomMapIsoOf (inferInstance : MonoidalClosed C) eK eL

/-- `internalHomMapIso` is the canonical uncurried internal-Hom bifunctor applied to the product
isomorphism. -/
theorem internalHomMapIso_uncurry_mapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    internalHomMapIso eK eL =
      (Functor.uncurry.obj MonoidalClosed.internalHom).mapIso
        (Iso.prod eK.op eL) :=
  internalHomMapIsoOf_uncurry_mapIso (inferInstance : MonoidalClosed C) eK eL

/-- The forward map of `internalHomMapIso` is the canonical two-variable internal-Hom map. -/
@[simp]
theorem internalHomMapIso_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (internalHomMapIso eK eL).hom = internalHomMap eK.hom eL.hom :=
  internalHomMapIsoOf_hom (inferInstance : MonoidalClosed C) eK eL

/-- The inverse of `internalHomMapIso` is the internal-Hom map on the inverse morphisms. -/
@[simp]
theorem internalHomMapIso_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ L₁ L₂ : C} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (internalHomMapIso eK eL).inv = internalHomMap eK.inv eL.inv :=
  internalHomMapIsoOf_inv (inferInstance : MonoidalClosed C) eK eL

/-- The canonical internal-Hom isomorphism induced by identity maps is the identity. -/
@[simp]
theorem internalHomMapIso_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (K L : C) :
    internalHomMapIso (Iso.refl K) (Iso.refl L) = Iso.refl _ :=
  internalHomMapIsoOf_refl (inferInstance : MonoidalClosed C) K L

/-- Canonical internal-Hom isomorphisms compose contravariantly in their source variable and
covariantly in their target variable. -/
theorem internalHomMapIso_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {K₁ K₂ K₃ L₁ L₂ L₃ : C}
    (eK₁ : K₂ ≅ K₁) (eK₂ : K₃ ≅ K₂)
    (eL₁ : L₁ ≅ L₂) (eL₂ : L₂ ≅ L₃) :
    internalHomMapIso (eK₂ ≪≫ eK₁) (eL₁ ≪≫ eL₂) =
      internalHomMapIso eK₁ eL₁ ≪≫ internalHomMapIso eK₂ eL₂ :=
  internalHomMapIsoOf_trans (inferInstance : MonoidalClosed C) eK₁ eK₂ eL₁ eL₂

end CategoryTheory.MonoidalClosed
