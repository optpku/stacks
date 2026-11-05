/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
public import ReasLib.CategoryTheory.Adjunction.RightIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit-owner internal-Hom functors and unit comparisons
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory
noncomputable section
universe v u
namespace CategoryTheory.MonoidalClosed

/-- The internal-Hom bifunctor selected by an explicit closed-monoidal owner.  This is the
instance-free whole-functor entry for APIs that carry a chosen `MonoidalClosed C` as ordinary
data. -/
@[stacks 0A65 "selected internal-Hom bifunctor"]
abbrev internalHomOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) : Cᵒᵖ ⥤ C ⥤ C :=
  @MonoidalClosed.internalHom C _ _ H

/-- The coherent tensor/internal-Hom parametrized adjunction selected by an explicit
closed-monoidal owner.  Unlike a family of pointwise adjunctions, this retains Mathlib's
naturality in the tensor parameter. -/
@[stacks 0A67 "selected tensor/internal-Hom adjunction"]
abbrev adj₂Of
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) :
    curriedTensor C ⊣₂ internalHomOf H :=
  @MonoidalClosed.internalHomAdjunction₂ C _ _ H

/-- The fixed-parameter internal-Hom functor selected by an explicit closed-monoidal owner.  This
is the instance-free entry for APIs that carry a chosen `MonoidalClosed C` as ordinary data. -/
@[stacks 0A65 "fixed-parameter internal-Hom functor"]
abbrev ihomOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K : C) : C ⥤ C :=
  (internalHomOf H).obj (Opposite.op K)

/-- The tensor/internal-Hom adjunction selected by an explicit closed-monoidal owner. -/
@[stacks 0A67 "fixed tensor/internal-Hom adjunction"]
noncomputable def adjunctionOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K : C) :
    MonoidalCategory.tensorLeft K ⊣ ihomOf H K :=
  (adj₂Of H).adj K

/-- Precomposition between internal-Hom functors selected by an explicit closed-monoidal owner. -/
@[stacks 0A65 "internal-Hom precomposition"]
noncomputable abbrev preOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (f : K₂ ⟶ K₁) :
    ihomOf H K₁ ⟶ ihomOf H K₂ :=
  @pre C _ _ K₁ K₂ (@MonoidalClosed.closed C _ _ H K₁)
    (@MonoidalClosed.closed C _ _ H K₂) f

/-- The explicit-owner precomposition induced by an identity is the identity natural
transformation. -/
@[simp]
theorem preOf_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K : C) :
    preOf H (𝟙 K) = 𝟙 (ihomOf H K) :=
  @MonoidalClosed.pre_id C _ _ K (@MonoidalClosed.closed C _ _ H K)

/-- Explicit-owner precomposition is contravariantly functorial in its source parameter. -/
theorem preOf_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K₃ : C}
    (f : K₂ ⟶ K₁) (g : K₃ ⟶ K₂) :
    preOf H (g ≫ f) = preOf H f ≫ preOf H g :=
  @MonoidalClosed.pre_map C _ _ K₃ K₂ K₁
    (@MonoidalClosed.closed C _ _ H K₃)
    (@MonoidalClosed.closed C _ _ H K₂)
    (@MonoidalClosed.closed C _ _ H K₁) g f

/-- Explicit-owner precomposition commutes with maps in the target variable. -/
@[reassoc]
theorem preOf_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂) :
    (preOf H f).app L₁ ≫ (ihomOf H K₂).map g =
      (ihomOf H K₁).map g ≫ (preOf H f).app L₂ :=
  @MonoidalClosed.pre_comm_ihom_map C _ _ K₂ K₁ L₁ L₂
    (@MonoidalClosed.closed C _ _ H K₂)
    (@MonoidalClosed.closed C _ _ H K₁) f g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Parameter naturality for the right-tensor adjunction obtained from an explicit closed owner
by transporting its left-tensor adjunction across the braiding. -/
@[stacks 0GWJ "explicit closed right-tensor adjunction parameter naturality"]
theorem adjunctionOf_right_homEquiv_naturality_one
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {X Y W Z : C} (f : X ⟶ Y) (g : W ⊗ Y ⟶ Z) :
    (((adjunctionOf H X).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight X)).homEquiv W Z) (W ◁ f ≫ g) =
      (((adjunctionOf H Y).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv W Z) g ≫
        (preOf H f).app Z := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply]
  change ((MonoidalClosed.internalHomAdjunction₂.adj X).homEquiv W Z)
      ((β_ X W).hom ≫ W ◁ f ≫ g) =
    ((MonoidalClosed.internalHomAdjunction₂.adj Y).homEquiv W Z)
      ((β_ Y W).hom ≫ g) ≫ (MonoidalClosed.internalHom.map f.op).app Z
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]
  exact MonoidalClosed.internalHomAdjunction₂.homEquiv_naturality_one
    f ((β_ Y W).hom ≫ g)

/-- The fixed-target internal-Hom functor in the contravariant source variable, selected by an
explicit closed-monoidal owner. -/
noncomputable abbrev sourceFunctorOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (L : C) : Cᵒᵖ ⥤ C :=
  (Functor.flip (internalHomOf H)).obj L

/-- The object formula for the explicit-owner source-variable internal-Hom functor. -/
@[simp]
theorem sourceFunctorOf_obj
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (L K : C) :
    (sourceFunctorOf H L).obj (Opposite.op K) = (ihomOf H K).obj L := rfl

/-- The map formula for the explicit-owner source-variable internal-Hom functor. -/
theorem sourceFunctorOf_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L : C} (f : K₂ ⟶ K₁) :
    (sourceFunctorOf H L).map f.op = (preOf H f).app L := rfl

/-- Postcomposition in the target variable, packaged as a natural transformation between the
source-variable functors selected by an explicit closed-monoidal owner. -/
noncomputable abbrev postOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    sourceFunctorOf H L₁ ⟶ sourceFunctorOf H L₂ :=
  (Functor.flip (internalHomOf H)).map f

/-- Identity target maps induce the identity source-variable natural transformation. -/
@[simp]
theorem postOf_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (L : C) :
    postOf H (𝟙 L) = 𝟙 (sourceFunctorOf H L) :=
  (Functor.flip (internalHomOf H)).map_id L

/-- Postcomposition is covariantly functorial in the target variable. -/
theorem postOf_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ L₃ : C}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    postOf H (f ≫ g) = postOf H f ≫ postOf H g :=
  (Functor.flip (internalHomOf H)).map_comp f g

/-- The component of explicit-owner postcomposition is the selected internal-Hom map. -/
@[simp]
theorem postOf_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (f : L₁ ⟶ L₂)
    (K : C) :
    (postOf H f).app (Opposite.op K) = (ihomOf H K).map f := rfl

/-- Explicit-owner postcomposition is natural in the contravariant source variable. -/
@[reassoc]
theorem postOf_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ L₁ L₂ : C}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    (sourceFunctorOf H L₁).map fK.op ≫
        (postOf H fL).app (Opposite.op K₂) =
      (postOf H fL).app (Opposite.op K₁) ≫
        (sourceFunctorOf H L₂).map fK.op :=
  (postOf H fL).naturality fK.op

/-- The component of explicit-owner precomposition by an identity is the identity morphism. -/
@[simp]
theorem preOf_id_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K L : C) :
    (preOf H (𝟙 K)).app L = 𝟙 (ihomOf H K).obj L := by
  simpa using NatTrans.congr_app (preOf_id H K) L

/-- The components of explicit-owner precomposition reverse source-map composition. -/
@[simp]
theorem preOf_comp_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K₃ : C}
    (f : K₂ ⟶ K₁) (g : K₃ ⟶ K₂) (L : C) :
    (preOf H (g ≫ f)).app L =
      (preOf H f).app L ≫ (preOf H g).app L := by
  simpa using NatTrans.congr_app (preOf_comp H f g) L

/-- An isomorphism of internal-Hom source objects induces the contravariant isomorphism of
selected internal-Hom functors. -/
noncomputable abbrev preIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    ihomOf H K₁ ≅ ihomOf H K₂ :=
  (internalHomOf H).mapIso e.symm.op

/-- The forward component of `preIsoOf` is precomposition by the inverse source isomorphism. -/
@[simp]
theorem preIsoOf_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (e : K₁ ≅ K₂) (L : C) :
    (preIsoOf H e).hom.app L = (preOf H e.inv).app L := rfl

/-- The inverse component of `preIsoOf` is precomposition by the forward source isomorphism. -/
@[simp]
theorem preIsoOf_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (e : K₁ ≅ K₂) (L : C) :
    (preIsoOf H e).inv.app L = (preOf H e.hom).app L := rfl

/-- The forward natural transformation of `preIsoOf` is precomposition by the inverse source
isomorphism. -/
@[simp]
theorem preIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    (preIsoOf H e).hom = preOf H e.inv := rfl

/-- The inverse natural transformation of `preIsoOf` is precomposition by the forward source
isomorphism. -/
@[simp]
theorem preIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ : C} (e : K₁ ≅ K₂) :
    (preIsoOf H e).inv = preOf H e.hom := rfl

/-- The explicit-owner target-variable isomorphism induced by an identity source is the
identity. -/
@[simp]
theorem preIsoOf_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (K : C) :
    preIsoOf H (Iso.refl K) = Iso.refl _ := by
  apply Iso.ext
  change preOf H (𝟙 K) = 𝟙 (ihomOf H K)
  exact preOf_id H K

/-- Explicit-owner target-variable isomorphisms compose contravariantly in the source
parameter. -/
theorem preIsoOf_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {K₁ K₂ K₃ : C}
    (e₁ : K₁ ≅ K₂) (e₂ : K₂ ≅ K₃) :
    preIsoOf H (e₁ ≪≫ e₂) = preIsoOf H e₁ ≪≫ preIsoOf H e₂ := by
  ext
  exact NatTrans.congr_app (preOf_comp H e₁.inv e₂.inv) _

/-- An isomorphism of internal-Hom target objects induces the covariant isomorphism of
source-variable functors selected by an explicit closed-monoidal owner. -/
noncomputable abbrev postIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    sourceFunctorOf H L₁ ≅ sourceFunctorOf H L₂ :=
  (Functor.flip (internalHomOf H)).mapIso e

/-- The forward component of `postIsoOf` is postcomposition by the forward target
isomorphism. -/
@[simp]
theorem postIsoOf_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (e : L₁ ≅ L₂) (K : C) :
    (postIsoOf H e).hom.app (Opposite.op K) = (ihomOf H K).map e.hom := rfl

/-- The inverse component of `postIsoOf` is postcomposition by the inverse target
isomorphism. -/
@[simp]
theorem postIsoOf_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (e : L₁ ≅ L₂) (K : C) :
    (postIsoOf H e).inv.app (Opposite.op K) = (ihomOf H K).map e.inv := rfl

/-- The forward natural transformation of `postIsoOf` is explicit-owner postcomposition by the
forward target isomorphism. -/
@[simp]
theorem postIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (postIsoOf H e).hom = postOf H e.hom := rfl

/-- The inverse natural transformation of `postIsoOf` is explicit-owner postcomposition by the
inverse target isomorphism. -/
@[simp]
theorem postIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (postIsoOf H e).inv = postOf H e.inv := rfl

/-- The explicit-owner source-variable isomorphism induced by an identity target is the identity. -/
@[simp]
theorem postIsoOf_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (L : C) :
    postIsoOf H (Iso.refl L) = Iso.refl _ := by
  ext
  simp

/-- Explicit-owner source-variable isomorphisms compose in the target parameter. -/
theorem postIsoOf_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {L₁ L₂ L₃ : C}
    (e₁ : L₁ ≅ L₂) (e₂ : L₂ ≅ L₃) :
    postIsoOf H (e₁ ≪≫ e₂) = postIsoOf H e₁ ≪≫ postIsoOf H e₂ := by
  ext
  exact NatTrans.congr_app ((Functor.flip (internalHomOf H)).map_comp e₁.hom e₂.hom) _

/-- The internal-Hom/unit comparison selected by an explicit closed-monoidal owner. -/
noncomputable abbrev unitNatIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) :
    𝟭 C ≅ ihomOf H (𝟙_ C) :=
  @MonoidalClosed.unitNatIso C _ _
    (@MonoidalClosed.closed C _ _ H (𝟙_ C))

/-- Transport the selected internal Hom out of an object identified with the tensor unit to the
identity functor. -/
noncomputable def ihomUnitIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) :
    ihomOf H U ≅ 𝟭 C :=
  (internalHomOf H).mapIso s.symm.op ≪≫ (unitNatIsoOf H).symm

/-- The forward component of `ihomUnitIsoOf` first precomposes along the inverse unit
identification and then applies the selected internal-Hom/unit comparison. -/
@[simp]
theorem ihomUnitIsoOf_hom_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) (K : C) :
    (ihomUnitIsoOf H s).hom.app K =
      (preOf H s.inv).app K ≫ (unitNatIsoOf H).inv.app K := rfl

/-- The inverse component of `ihomUnitIsoOf` applies the selected internal-Hom/unit comparison
and then precomposes along the forward unit identification. -/
@[simp]
theorem ihomUnitIsoOf_inv_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) (K : C) :
    (ihomUnitIsoOf H s).inv.app K =
      (unitNatIsoOf H).hom.app K ≫ (preOf H s.hom).app K := rfl

/-- The forward natural transformation of `ihomUnitIsoOf` is source precomposition followed by
the selected internal-Hom/unit comparison. -/
@[simp]
theorem ihomUnitIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) :
    (ihomUnitIsoOf H s).hom = preOf H s.inv ≫ (unitNatIsoOf H).inv := rfl

/-- The inverse natural transformation of `ihomUnitIsoOf` is the selected internal-Hom/unit
comparison followed by source precomposition. -/
@[simp]
theorem ihomUnitIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) :
    (ihomUnitIsoOf H s).inv = (unitNatIsoOf H).hom ≫ preOf H s.hom := rfl

/-- Transporting the selected internal Hom along the identity of the tensor unit recovers the
inverse selected internal-Hom/unit comparison. -/
@[simp]
theorem ihomUnitIsoOf_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) :
    ihomUnitIsoOf H (Iso.refl (𝟙_ C)) = (unitNatIsoOf H).symm := by
  apply Iso.ext
  rw [ihomUnitIsoOf_hom]
  change preOf H (𝟙 (𝟙_ C)) ≫ (unitNatIsoOf H).inv = (unitNatIsoOf H).inv
  rw [preOf_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right-adjoint comparison obtained from the braided right-tensor adjunction and a tensor
unit identification is the standard selected internal-Hom/unit comparison. -/
theorem rightAdjointUniq_ofBraidedClosedOf_unit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) :
    (((RightInternalHom.ofBraidedClosedOf H).adj₂.adj U).ofNatIsoLeft
      (((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C)).rightAdjointUniq
        Adjunction.id = ihomUnitIsoOf H s := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  apply Iso.ext
  ext K
  have huniq := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (((RightInternalHom.ofBraidedClosedOf H).adj₂.adj U).ofNatIsoLeft
      (((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C))
    Adjunction.id K
  change
    ((((RightInternalHom.ofBraidedClosedOf H).adj₂.adj U).ofNatIsoLeft
        (((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C)).rightAdjointUniq
      Adjunction.id).hom.app K ≫ 𝟙 K = _ at huniq
  have huniq' :
      ((((RightInternalHom.ofBraidedClosedOf H).adj₂.adj U).ofNatIsoLeft
          (((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C)).rightAdjointUniq
        Adjunction.id).hom.app K =
        (((RightInternalHom.ofBraidedClosedOf H).adj₂.adj U).ofNatIsoLeft
          (((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C)).counit.app K := by
    simpa only [Functor.id_obj, Category.comp_id] using huniq
  rw [huniq', Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  change
    ((((curriedTensor C).flip.mapIso s) ≪≫ rightUnitorNatIso C).inv.app
        ((ihomOf H U).obj K)) ≫
      (RightInternalHom.ofBraidedClosedOf H).ev U K =
      (preOf H s.inv).app K ≫ (unitNatIsoOf H).inv.app K
  rw [Iso.trans_inv, NatTrans.comp_app]
  rw [Category.assoc, RightInternalHom.ofBraidedClosed.ev]
  have hunitIso :
      (((ihom.adjunction (𝟙_ C)).ofNatIsoLeft
        (leftUnitorNatIso C)).rightAdjointUniq Adjunction.id) =
        (MonoidalClosed.unitNatIso (C := C)).symm := by
    apply Iso.ext
    ext X
    simp [Adjunction.rightAdjointUniq,
      CategoryTheory.MonoidalClosed.unitNatIso,
      CategoryTheory.conjugateIsoEquiv, CategoryTheory.conjugateEquiv,
      CategoryTheory.mateEquiv]
  have hunit :
      ((ihom.adjunction (𝟙_ C)).ofNatIsoLeft
        (leftUnitorNatIso C)).counit.app K =
          (MonoidalClosed.unitNatIso (C := C)).inv.app K := by
    rw [← NatTrans.congr_app (Adjunction.rightAdjointUniq_id_hom
      ((ihom.adjunction (𝟙_ C)).ofNatIsoLeft
        (leftUnitorNatIso C))) K]
    rw [NatTrans.congr_app (congrArg Iso.hom hunitIso) K]
    rfl
  have hunit' :
      (leftUnitorNatIso C).inv.app ((ihomOf H (𝟙_ C)).obj K) ≫
        (MonoidalClosed.adjunctionOf H (𝟙_ C)).counit.app K =
          (unitNatIsoOf H).inv.app K := by
    simpa only [MonoidalClosed.adjunctionOf, adj₂Of, ihomOf, internalHomOf,
      MonoidalClosed.internalHom, MonoidalClosed.internalHomAdjunction₂,
      unitNatIsoOf,
      Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app] using hunit
  change
    (rightUnitorNatIso C).inv.app ((ihomOf H U).obj K) ≫
      (((ihomOf H U).obj K) ◁ s.inv ≫
        ((β_ U ((ihomOf H U).obj K)).inv ≫
          (MonoidalClosed.adjunctionOf H U).counit.app K)) =
      (preOf H s.inv).app K ≫ (unitNatIsoOf H).inv.app K
  rw [BraidedCategory.braiding_inv_naturality_right_assoc]
  rw [braiding_inv_tensorUnit_left]
  simp only [rightUnitorNatIso, NatIso.ofComponents_inv_app,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hpre :
      (𝟙_ C) ◁ (preOf H s.inv).app K ≫
          (MonoidalClosed.adjunctionOf H (𝟙_ C)).counit.app K =
        s.inv ▷ ((ihomOf H U).obj K) ≫
          (MonoidalClosed.adjunctionOf H U).counit.app K := by
    simpa only [preOf, ihomOf, internalHomOf, MonoidalClosed.internalHom,
      MonoidalClosed.adjunctionOf, adj₂Of,
      MonoidalClosed.internalHomAdjunction₂,
      ihom.ihom_adjunction_counit] using
        (@MonoidalClosed.id_tensor_pre_app_comp_ev C _ _ U (𝟙_ C)
          (@MonoidalClosed.closed C _ _ H U)
          (@MonoidalClosed.closed C _ _ H (𝟙_ C)) s.inv K)
  rw [← hpre]
  rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc]
  simpa only [Functor.id_obj, leftUnitorNatIso,
    NatIso.ofComponents_inv_app] using congrArg
    (fun f => (preOf H s.inv).app K ≫ f) hunit'

/-- A map into an object whose selected internal Hom is the identity induces a natural
transformation from the identity by internal-Hom precomposition. -/
noncomputable def unitOfPre
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C}
    (unitIso : ihomOf H U ≅ 𝟭 C) (p : X ⟶ U) :
    𝟭 C ⟶ ihomOf H X :=
  unitIso.inv ≫ preOf H p

/-- Objectwise, the unit induced by `p` is the inverse explicit unit comparison followed by
selected internal-Hom precomposition along `p`. -/
@[simp]
theorem unitOfPre_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C}
    (unitIso : ihomOf H U ≅ 𝟭 C) (p : X ⟶ U) (K : C) :
    (unitOfPre H unitIso p).app K =
      unitIso.inv.app K ≫ (preOf H p).app K := rfl

/-- A selected internal-Hom unit induced by precomposition is natural in its target object. -/
@[reassoc]
theorem unitOfPre_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U K L : C}
    (unitIso : ihomOf H U ≅ 𝟭 C) (p : X ⟶ U) (f : K ⟶ L) :
    f ≫ (unitOfPre H unitIso p).app L =
      (unitOfPre H unitIso p).app K ≫ (ihomOf H X).map f :=
  (unitOfPre H unitIso p).naturality f

/-- Precomposing the source map composes the induced unit with selected internal-Hom
precomposition. -/
theorem unitOfPre_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X Y U : C}
    (unitIso : ihomOf H U ≅ 𝟭 C) (p : X ⟶ U) (q : Y ⟶ X) :
    unitOfPre H unitIso (q ≫ p) =
      unitOfPre H unitIso p ≫ preOf H q := by
  rw [unitOfPre, unitOfPre, preOf_comp, Category.assoc]

/-- The unit induced by the identity of its source is the inverse explicit unit comparison. -/
@[simp]
theorem unitOfPre_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) (U : C) (unitIso : ihomOf H U ≅ 𝟭 C) :
    unitOfPre H unitIso (𝟙 U) = unitIso.inv := by
  rw [unitOfPre, preOf_id, Category.comp_id]

/-- A map into an object explicitly identified with the tensor unit induces the selected
internal-Hom unit without requiring a separately chosen functor isomorphism. -/
noncomputable def unitOfPreOfIsoUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C} (s : U ≅ 𝟙_ C) (p : X ⟶ U) :
    𝟭 C ⟶ ihomOf H X :=
  unitOfPre H (ihomUnitIsoOf H s) p

/-- Objectwise formula for the selected internal-Hom unit constructed from an explicit
identification of its intermediate source with the tensor unit. -/
@[simp]
theorem unitOfPreOfIsoUnit_app
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C} (s : U ≅ 𝟙_ C) (p : X ⟶ U) (K : C) :
    (unitOfPreOfIsoUnit H s p).app K =
      (ihomUnitIsoOf H s).inv.app K ≫ (preOf H p).app K := rfl

/-- The selected internal-Hom unit obtained from `p : X ⟶ U` and `U ≅ 𝟙_ C` is the canonical
unit comparison followed by precomposition along their composite. -/
theorem unitOfPreOfIsoUnit_eq
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C} (s : U ≅ 𝟙_ C) (p : X ⟶ U) :
    unitOfPreOfIsoUnit H s p =
      (unitNatIsoOf H).hom ≫ preOf H (p ≫ s.hom) := by
  rw [unitOfPreOfIsoUnit, unitOfPre, ihomUnitIsoOf_inv, preOf_comp,
    Category.assoc]

/-- Objectwise normal form for the selected internal-Hom unit constructed from a map into an
object identified with the tensor unit. -/
theorem unitOfPreOfIsoUnit_app_expanded
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U : C} (s : U ≅ 𝟙_ C) (p : X ⟶ U) (K : C) :
    (unitOfPreOfIsoUnit H s p).app K =
      (unitNatIsoOf H).hom.app K ≫
        (preOf H (p ≫ s.hom)).app K := by
  simpa using NatTrans.congr_app (unitOfPreOfIsoUnit_eq H s p) K

/-- The unit constructed from an explicit tensor-unit identification is natural in its target
object. -/
@[reassoc]
theorem unitOfPreOfIsoUnit_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X U K L : C}
    (s : U ≅ 𝟙_ C) (p : X ⟶ U) (f : K ⟶ L) :
    f ≫ (unitOfPreOfIsoUnit H s p).app L =
      (unitOfPreOfIsoUnit H s p).app K ≫ (ihomOf H X).map f :=
  unitOfPre_naturality H (ihomUnitIsoOf H s) p f

/-- Precomposing the source map composes the unit constructed from a tensor-unit identification
with selected internal-Hom precomposition. -/
theorem unitOfPreOfIsoUnit_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {X Y U : C}
    (s : U ≅ 𝟙_ C) (p : X ⟶ U) (q : Y ⟶ X) :
    unitOfPreOfIsoUnit H s (q ≫ p) =
      unitOfPreOfIsoUnit H s p ≫ preOf H q :=
  unitOfPre_comp H (ihomUnitIsoOf H s) p q

/-- The selected internal-Hom unit induced by the identity of an object identified with the
tensor unit is the inverse transported unit comparison. -/
@[simp]
theorem unitOfPreOfIsoUnit_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {U : C} (s : U ≅ 𝟙_ C) :
    unitOfPreOfIsoUnit H s (𝟙 U) = (ihomUnitIsoOf H s).inv :=
  unitOfPre_id H U (ihomUnitIsoOf H s)

end CategoryTheory.MonoidalClosed
