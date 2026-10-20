module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
public import ReasLib.CategoryTheory.Adjunction.RightIso
public import ReasLib.CategoryTheory.Adjunction.Parametrized.Generated
public import ReasLib.CategoryTheory.Monoidal.Closed.Source
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.Source
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality API for closed monoidal categories

This leaf packages the two-variable functoriality of internal Homs and the mate construction for
any chosen family of left adjoints to them.  It deliberately does not assume that the left
adjoints are definitionally tensor functors, so it applies equally to transported or derived
tensor constructions.
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

/-- The tensor-to-endomorphism comparison selected by an explicit closed owner. -/
@[stacks 0FNY "explicit closed-owner tensor-to-endomorphism comparison"]
noncomputable def tensorIhomUnitToEndOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    X ⊗ (ihomOf H X).obj (𝟙_ C) ⟶ (ihomOf H X).obj X :=
  (β_ X ((ihomOf H X).obj (𝟙_ C))).hom ≫
    ((ihomOf H X).obj (𝟙_ C)) ◁
      (@unitIsoSelf C _ _ X (@MonoidalClosed.closed C _ _ H (𝟙_ C))).inv ≫
    @CategoryTheory.MonoidalClosed.comp C _ _ X (𝟙_ C) X
      (@MonoidalClosed.closed C _ _ H X)
      (@MonoidalClosed.closed C _ _ H (𝟙_ C))

/-- The explicit closed-owner tensor-to-endomorphism comparison unfolds to its braiding, unit
comparison, and enriched-composition composite. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison specification"]
theorem tensorIhomUnitToEndOf_spec
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    tensorIhomUnitToEndOf H X =
      (β_ X ((ihomOf H X).obj (𝟙_ C))).hom ≫
        ((ihomOf H X).obj (𝟙_ C)) ◁
          (@unitIsoSelf C _ _ X (@MonoidalClosed.closed C _ _ H (𝟙_ C))).inv ≫
        @CategoryTheory.MonoidalClosed.comp C _ _ X (𝟙_ C) X
          (@MonoidalClosed.closed C _ _ H X)
          (@MonoidalClosed.closed C _ _ H (𝟙_ C)) := rfl

/-- The explicit closed-owner tensor-to-endomorphism comparison is the source-order
tensor/internal-Hom comparison followed by the right unitor in its target. -/
@[stacks 0FNY "explicit tensor-to-endomorphism source-order formula"]
theorem tensorIhomUnitToEndOf_eq_sourceTensor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C) :
    tensorIhomUnitToEndOf H X =
      @Source.tensor C _ _ _ H X (𝟙_ C) X ≫
        (ihomOf H X).map (ρ_ X).hom := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the definitional reduction used by this proof.
  letI : MonoidalClosed C := H
  change tensorIhomUnitToEnd X =
    Source.tensor X (𝟙_ C) X ≫ (ihom X).map (ρ_ X).hom
  exact CategoryTheory.MonoidalClosed.Dual.tensorIhomUnitToEnd_eq_sourceTensor X

/-- The inverse of the explicit closed-owner tensor-to-endomorphism comparison. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison inverse"]
noncomputable def tensorIhomUnitToEndInvOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomOf H X).obj X ⟶ X ⊗ (ihomOf H X).obj (𝟙_ C) :=
  CategoryTheory.inv (tensorIhomUnitToEndOf H X)

/-- The explicit closed-owner tensor-to-endomorphism comparison followed by its inverse is the
identity. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism forward-inverse law"]
theorem tensorIhomUnitToEndOf_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    tensorIhomUnitToEndOf H X ≫ tensorIhomUnitToEndInvOf H X = 𝟙 _ :=
  IsIso.hom_inv_id (tensorIhomUnitToEndOf H X)

/-- The inverse of the explicit closed-owner tensor-to-endomorphism comparison followed by the
comparison is the identity. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism inverse-forward law"]
theorem tensorIhomUnitToEndOf_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    tensorIhomUnitToEndInvOf H X ≫ tensorIhomUnitToEndOf H X = 𝟙 _ :=
  IsIso.inv_hom_id (tensorIhomUnitToEndOf H X)

/-- The explicit closed-owner tensor-to-endomorphism comparison packaged as an isomorphism. -/
@[stacks 0FNY "explicit tensor-to-endomorphism comparison isomorphism"]
noncomputable def tensorIhomUnitToEndIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    X ⊗ (ihomOf H X).obj (𝟙_ C) ≅ (ihomOf H X).obj X where
  hom := tensorIhomUnitToEndOf H X
  inv := tensorIhomUnitToEndInvOf H X
  hom_inv_id := tensorIhomUnitToEndOf_hom_inv_id H X
  inv_hom_id := tensorIhomUnitToEndOf_inv_hom_id H X

/-- The forward map of the explicit tensor-to-endomorphism isomorphism. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism isomorphism hom"]
theorem tensorIhomUnitToEndIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (tensorIhomUnitToEndIsoOf H X).hom = tensorIhomUnitToEndOf H X := rfl

/-- The inverse map of the explicit tensor-to-endomorphism isomorphism. -/
@[simp, stacks 0FNY "explicit tensor-to-endomorphism isomorphism inverse"]
theorem tensorIhomUnitToEndIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (tensorIhomUnitToEndIsoOf H X).inv = tensorIhomUnitToEndInvOf H X := rfl

/-- The coevaluation associated with an explicit tensor-to-endomorphism inverse. -/
@[stacks 0FNY "explicit closed-owner internal-Hom coevaluation"]
noncomputable def ihomUnitCoevaluationOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    𝟙_ C ⟶ (ihomOf H X).obj (𝟙_ C) ⊗ X :=
  @curry' C _ _ X X (@MonoidalClosed.closed C _ _ H X) (𝟙 X) ≫
    tensorIhomUnitToEndInvOf H X ≫
      (β_ X ((ihomOf H X).obj (𝟙_ C))).hom

/-- The first triangle identity for the explicit-owner internal-Hom exact pairing. -/
@[stacks 0FNY "explicit internal-Hom pairing first triangle"]
theorem ihomUnitExactPairingOf_coevaluation_evaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    X ◁ ihomUnitCoevaluationOf H X ≫
        (α_ X ((ihomOf H X).obj (𝟙_ C)) X).inv ≫
          ((@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C)) ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the chosen tensor/internal-Hom adjunction used by this proof.
  letI : MonoidalClosed C := H
  -- Local instance justification (proof-local temporary data): install the derived `IsIso` fact
  -- only for the tensor/internal-Hom pairing calculation in this proof.
  letI : IsIso (tensorIhomUnitToEnd X) := by
    change IsIso (tensorIhomUnitToEndOf H X)
    infer_instance
  change X ◁ ihomUnitCoevaluation X ≫
      (α_ X ((ihom X).obj (𝟙_ C)) X).inv ≫
        ((ihom.ev X).app (𝟙_ C)) ▷ X =
    (ρ_ X).hom ≫ (λ_ X).inv
  exact (@ihomUnitExactPairing C _ _ _ _ X _).coevaluation_evaluation'

/-- The second triangle identity for the explicit-owner internal-Hom exact pairing. -/
@[stacks 0FNY "explicit internal-Hom pairing second triangle"]
theorem ihomUnitExactPairingOf_evaluation_coevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    ihomUnitCoevaluationOf H X ▷ ((ihomOf H X).obj (𝟙_ C)) ≫
        (α_ ((ihomOf H X).obj (𝟙_ C)) X ((ihomOf H X).obj (𝟙_ C))).hom ≫
          ((ihomOf H X).obj (𝟙_ C)) ◁
            (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C) =
      (λ_ ((ihomOf H X).obj (𝟙_ C))).hom ≫
        (ρ_ ((ihomOf H X).obj (𝟙_ C))).inv := by
  -- Local instance justification (defeq pin): pin the explicit `MonoidalClosed` owner `H` for
  -- the chosen tensor/internal-Hom adjunction used by this proof.
  letI : MonoidalClosed C := H
  -- Local instance justification (proof-local temporary data): install the derived `IsIso` fact
  -- only for the tensor/internal-Hom pairing calculation in this proof.
  letI : IsIso (tensorIhomUnitToEnd X) := by
    change IsIso (tensorIhomUnitToEndOf H X)
    infer_instance
  change ihomUnitCoevaluation X ▷ ((ihom X).obj (𝟙_ C)) ≫
      (α_ ((ihom X).obj (𝟙_ C)) X ((ihom X).obj (𝟙_ C))).hom ≫
        ((ihom X).obj (𝟙_ C)) ◁ (ihom.ev X).app (𝟙_ C) =
    (λ_ ((ihom X).obj (𝟙_ C))).hom ≫ (ρ_ ((ihom X).obj (𝟙_ C))).inv
  exact (@ihomUnitExactPairing C _ _ _ _ X _).evaluation_coevaluation'

/-- The exact pairing furnished by an explicit closed owner and an invertible
tensor-to-endomorphism comparison. -/
@[reducible, stacks 0FNY "explicit internal-Hom exact pairing"]
noncomputable def ihomUnitExactPairingOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    ExactPairing ((ihomOf H X).obj (𝟙_ C)) X where
  coevaluation' := ihomUnitCoevaluationOf H X
  evaluation' := (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C)
  coevaluation_evaluation' := ihomUnitExactPairingOf_coevaluation_evaluation H X
  evaluation_coevaluation' := ihomUnitExactPairingOf_evaluation_coevaluation H X

/-- The coevaluation projection of the explicit-owner internal-Hom exact pairing. -/
@[simp, stacks 0FNY "explicit internal-Hom pairing coevaluation projection"]
theorem ihomUnitExactPairingOf_coevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomUnitExactPairingOf H X).coevaluation' =
      ihomUnitCoevaluationOf H X := rfl

/-- The evaluation projection of the explicit-owner internal-Hom exact pairing. -/
@[simp, stacks 0FNY "explicit internal-Hom pairing evaluation projection"]
theorem ihomUnitExactPairingOf_evaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    (H : MonoidalClosed C) (X : C)
    [IsIso (tensorIhomUnitToEndOf H X)] :
    (ihomUnitExactPairingOf H X).evaluation' =
      (@MonoidalClosed.closed C _ _ H X).adj.counit.app (𝟙_ C) := rfl

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

/-- A morphism of internal-Hom parameters induces a map between a chosen family of left adjoints,
with the closed-monoidal owner supplied explicitly. -/
noncomputable def leftAdjointMapOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    T L₁ ⟶ T L₂ :=
  ParametrizedAdjunction.leftAdjointMap (internalHomOf H) adj f

/-- Under the first explicit-owner adjunction, `leftAdjointMapOf` is the second unit followed by
precomposition on the internal Hom. -/
theorem leftAdjointMapOf_homEquiv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂) (K : C) :
    (adj L₁).homEquiv K ((T L₂).obj K) ((leftAdjointMapOf H adj f).app K) =
      (adj L₂).unit.app K ≫ (preOf H f).app ((T L₂).obj K) := by
  have h :
      (adj L₁).homEquiv K ((T L₂).obj K)
          ((leftAdjointMapOf H adj f).app K ≫ 𝟙 ((T L₂).obj K)) =
        (adj L₂).homEquiv K ((T L₂).obj K) (𝟙 ((T L₂).obj K)) ≫
          (preOf H f).app ((T L₂).obj K) :=
    ParametrizedAdjunction.leftAdjointMap_homEquiv_naturality
      (internalHomOf H) adj f (𝟙 ((T L₂).obj K))
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  exact h

/-- The inverse mate formula for an arbitrary target map into the second internal-Hom object.
This is the form needed when a family of pointwise adjunctions is assembled into a
`ParametrizedAdjunction`; it avoids reconstructing the transpose calculation at each use site. -/
@[reassoc]
theorem leftAdjointMapOf_homEquiv_symm
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂)
    {K N : C} (g : K ⟶ (ihomOf H L₂).obj N) :
    (leftAdjointMapOf H adj f).app K ≫ ((adj L₂).homEquiv K N).symm g =
      ((adj L₁).homEquiv K N).symm (g ≫ (preOf H f).app N) :=
  ParametrizedAdjunction.leftAdjointMap_homEquiv_symm
    (internalHomOf H) adj f g

/-- The arbitrary-map form of the parameter naturality for `leftAdjointMapOf`.  This is the exact
`ParametrizedAdjunction.mk'` input and is useful when the target map is not an identity. -/
@[reassoc]
theorem leftAdjointMapOf_homEquiv_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂)
    {K N : C} (g : (T L₂).obj K ⟶ N) :
    (adj L₁).homEquiv K N ((leftAdjointMapOf H adj f).app K ≫ g) =
      (adj L₂).homEquiv K N g ≫ (preOf H f).app N :=
  ParametrizedAdjunction.leftAdjointMap_homEquiv_naturality
    (internalHomOf H) adj f g

/-- The explicit-owner left-adjoint map induced by an identity parameter is the identity. -/
@[simp]
theorem leftAdjointMapOf_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) (L : C) :
    leftAdjointMapOf H adj (𝟙 L) = 𝟙 _ :=
  ParametrizedAdjunction.leftAdjointMap_id (internalHomOf H) adj L

/-- Explicit-owner left-adjoint maps compose in the same order as their parameter morphisms. -/
@[reassoc]
theorem leftAdjointMapOf_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L)
    {L₁ L₂ L₃ : C} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    leftAdjointMapOf H adj (f ≫ g) =
      leftAdjointMapOf H adj f ≫ leftAdjointMapOf H adj g :=
  ParametrizedAdjunction.leftAdjointMap_comp (internalHomOf H) adj f g

/-- The functor on left adjoints generated by an explicit family of pointwise adjunctions.
Its morphism part is the mate `leftAdjointMapOf`; it is intentionally a named generated owner and
is not identified with any independently chosen functor. -/
noncomputable abbrev leftAdjointFunctorOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) : C ⥤ C ⥤ C :=
  ParametrizedAdjunction.leftAdjointFunctor (internalHomOf H) adj

/-- The parametrized adjunction generated by an explicit family of pointwise left adjoints.
Use `leftAdjointFunctorOf` when the generated morphism data must remain visible; this declaration
does not assert equality with another pre-existing functor carrying the same object assignment. -/
noncomputable abbrev parametrizedAdjunctionOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) :
    leftAdjointFunctorOf H adj ⊣₂ internalHomOf H :=
  ParametrizedAdjunction.ofPointwiseLeftAdjoints (internalHomOf H) adj

/-- The explicit-owner generated left-adjoint functor specializes at a parameter to the chosen
pointwise left-adjoint functor. -/
@[simp]
theorem leftAdjointFunctorOf_obj
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) (L : C) :
    (leftAdjointFunctorOf H adj).obj L = T L := rfl

/-- The morphism part of the explicit-owner generated left-adjoint functor is the canonical mate
map. -/
@[simp]
theorem leftAdjointFunctorOf_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    (leftAdjointFunctorOf H adj).map f = leftAdjointMapOf H adj f := rfl

/-- The component of the explicit-owner generated parametrized adjunction is the supplied
pointwise adjunction. -/
@[simp]
theorem parametrizedAdjunctionOf_adj
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) (L : C) :
    (parametrizedAdjunctionOf H adj).adj L = adj L := rfl

/-- An explicit-owner left-adjoint map induced by an isomorphism is itself an isomorphism. -/
instance isIso_leftAdjointMapOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (f : L₁ ⟶ L₂) [IsIso f] :
    IsIso (leftAdjointMapOf H adj f) :=
  ParametrizedAdjunction.isIso_leftAdjointMap (internalHomOf H) adj f

/-- Explicit-owner mate maps induced by an isomorphism and its inverse compose to the identity on
the source left adjoint. -/
theorem leftAdjointMapIsoOf_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    leftAdjointMapOf H adj e.hom ≫ leftAdjointMapOf H adj e.inv = 𝟙 _ :=
  ParametrizedAdjunction.leftAdjointMapIso_hom_inv_id
    (internalHomOf H) adj e

/-- Explicit-owner mate maps induced by the inverse of an isomorphism and by the isomorphism
compose to the identity on the target left adjoint. -/
theorem leftAdjointMapIsoOf_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    leftAdjointMapOf H adj e.inv ≫ leftAdjointMapOf H adj e.hom = 𝟙 _ :=
  ParametrizedAdjunction.leftAdjointMapIso_inv_hom_id
    (internalHomOf H) adj e

/-- An explicit-owner left-adjoint map packaged as a natural isomorphism. -/
noncomputable def leftAdjointMapIsoOf
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    T L₁ ≅ T L₂ :=
  ParametrizedAdjunction.leftAdjointMapIso (internalHomOf H) adj e

/-- The forward map of `leftAdjointMapIsoOf` is its explicit-owner mate map. -/
@[simp]
theorem leftAdjointMapIsoOf_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointMapIsoOf H adj e).hom = leftAdjointMapOf H adj e.hom :=
  ParametrizedAdjunction.leftAdjointMapIso_hom (internalHomOf H) adj e

/-- The inverse of `leftAdjointMapIsoOf` is its mate map on the inverse parameter. -/
@[simp]
theorem leftAdjointMapIsoOf_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointMapIsoOf H adj e).inv = leftAdjointMapOf H adj e.inv :=
  ParametrizedAdjunction.leftAdjointMapIso_inv (internalHomOf H) adj e

/-- The explicit-owner left-adjoint isomorphism induced by an identity parameter is the identity. -/
@[simp]
theorem leftAdjointMapIsoOf_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) (L : C) :
    leftAdjointMapIsoOf H adj (Iso.refl L) = Iso.refl _ := by
  ext
  simp

/-- Explicit-owner left-adjoint isomorphisms compose in the parameter. -/
theorem leftAdjointMapIsoOf_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L)
    {L₁ L₂ L₃ : C} (e₁ : L₁ ≅ L₂) (e₂ : L₂ ≅ L₃) :
    leftAdjointMapIsoOf H adj (e₁ ≪≫ e₂) =
      leftAdjointMapIsoOf H adj e₁ ≪≫ leftAdjointMapIsoOf H adj e₂ := by
  ext
  exact NatTrans.congr_app (leftAdjointMapOf_comp H adj e₁.hom e₂.hom) _

/-- The generated explicit-owner functor maps a parameter isomorphism to its mate isomorphism. -/
@[simp]
theorem leftAdjointFunctorOf_mapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (H : MonoidalClosed C) {T : C → C ⥤ C}
    (adj : ∀ L, T L ⊣ ihomOf H L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointFunctorOf H adj).mapIso e = leftAdjointMapIsoOf H adj e := rfl

/-- Given a family of left adjoints to the internal-Hom functors, a morphism of internal-Hom
parameters induces the corresponding morphism between the left adjoints. -/
noncomputable def leftAdjointMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    T L₁ ⟶ T L₂ :=
  leftAdjointMapOf (inferInstance : MonoidalClosed C) adj f

/-- Under the first adjunction, `leftAdjointMap` is the unit for the second adjunction followed
by precomposition on the internal Hom. -/
theorem leftAdjointMap_homEquiv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) (K : C) :
    (adj L₁).homEquiv K ((T L₂).obj K) ((leftAdjointMap adj f).app K) =
      (adj L₂).unit.app K ≫ (pre f).app ((T L₂).obj K) :=
  leftAdjointMapOf_homEquiv (inferInstance : MonoidalClosed C) adj f K

/-- The inverse canonical mate formula for an arbitrary target map into the second internal-Hom
object. -/
@[reassoc]
theorem leftAdjointMap_homEquiv_symm
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) {K N : C}
    (g : K ⟶ (ihom L₂).obj N) :
    (leftAdjointMap adj f).app K ≫ ((adj L₂).homEquiv K N).symm g =
      ((adj L₁).homEquiv K N).symm (g ≫ (pre f).app N) :=
  leftAdjointMapOf_homEquiv_symm
    (inferInstance : MonoidalClosed C) adj f g

/-- The arbitrary-map parameter naturality formula for the canonical `leftAdjointMap`. -/
@[reassoc]
theorem leftAdjointMap_homEquiv_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) {K N : C}
    (g : (T L₂).obj K ⟶ N) :
    (adj L₁).homEquiv K N ((leftAdjointMap adj f).app K ≫ g) =
      (adj L₂).homEquiv K N g ≫ (pre f).app N :=
  leftAdjointMapOf_homEquiv_naturality
    (inferInstance : MonoidalClosed C) adj f g

/-- The left-adjoint map induced by an identity internal-Hom parameter is the identity. -/
@[simp]
theorem leftAdjointMap_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) (L : C) :
    leftAdjointMap adj (𝟙 L) = 𝟙 _ :=
  leftAdjointMapOf_id (inferInstance : MonoidalClosed C) adj L

/-- Left-adjoint maps induced by internal-Hom parameters compose in the same order as their
parameter morphisms. -/
@[reassoc]
theorem leftAdjointMap_comp
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ L₃ : C} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    leftAdjointMap adj (f ≫ g) = leftAdjointMap adj f ≫ leftAdjointMap adj g :=
  leftAdjointMapOf_comp (inferInstance : MonoidalClosed C) adj f g

/-- The canonical functor on a family of chosen left adjoints to the ambient internal-Hom
functors.  Its morphism part is `leftAdjointMap`. -/
noncomputable abbrev leftAdjointFunctor
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) : C ⥤ C ⥤ C :=
  leftAdjointFunctorOf (inferInstance : MonoidalClosed C) adj

/-- The canonical parametrized adjunction generated by a family of pointwise left adjoints to
the ambient internal-Hom functors. -/
noncomputable abbrev parametrizedAdjunction
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) :
    leftAdjointFunctor adj ⊣₂ MonoidalClosed.internalHom :=
  parametrizedAdjunctionOf (inferInstance : MonoidalClosed C) adj

/-- The canonical generated left-adjoint functor specializes at a parameter to the supplied
pointwise left adjoint. -/
@[simp]
theorem leftAdjointFunctor_obj
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) (L : C) :
    (leftAdjointFunctor adj).obj L = T L := rfl

/-- The morphism part of the canonical generated left-adjoint functor is `leftAdjointMap`. -/
@[simp]
theorem leftAdjointFunctor_map
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) :
    (leftAdjointFunctor adj).map f = leftAdjointMap adj f := rfl

/-- Each component of the canonical generated parametrized adjunction is the supplied pointwise
adjunction. -/
@[simp]
theorem parametrizedAdjunction_adj
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) (L : C) :
    (parametrizedAdjunction adj).adj L = adj L := rfl

/-- A left-adjoint map induced by an isomorphism of internal-Hom parameters is itself an
isomorphism. -/
instance isIso_leftAdjointMap
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (f : L₁ ⟶ L₂) [IsIso f] :
    IsIso (leftAdjointMap adj f) :=
  isIso_leftAdjointMapOf (inferInstance : MonoidalClosed C) adj f

/-- The left-adjoint mate maps induced by an isomorphism and its inverse compose to the identity on
the source left adjoint. -/
theorem leftAdjointMapIso_hom_inv_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    leftAdjointMap adj e.hom ≫ leftAdjointMap adj e.inv = 𝟙 _ :=
  leftAdjointMapIsoOf_hom_inv_id
    (inferInstance : MonoidalClosed C) adj e

/-- The left-adjoint mate maps induced by the inverse of an isomorphism and by the isomorphism
compose to the identity on the target left adjoint. -/
theorem leftAdjointMapIso_inv_hom_id
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    leftAdjointMap adj e.inv ≫ leftAdjointMap adj e.hom = 𝟙 _ :=
  leftAdjointMapIsoOf_inv_hom_id
    (inferInstance : MonoidalClosed C) adj e

/-- A left-adjoint map packaged as a natural isomorphism when its parameter map is an
isomorphism. -/
noncomputable def leftAdjointMapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    T L₁ ≅ T L₂ :=
  leftAdjointMapIsoOf (inferInstance : MonoidalClosed C) adj e

/-- The forward map of `leftAdjointMapIso` is the canonical mate map. -/
@[simp]
theorem leftAdjointMapIso_hom
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointMapIso adj e).hom = leftAdjointMap adj e.hom :=
  leftAdjointMapIsoOf_hom (inferInstance : MonoidalClosed C) adj e

/-- The inverse of `leftAdjointMapIso` is the mate map induced by the inverse parameter. -/
@[simp]
theorem leftAdjointMapIso_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointMapIso adj e).inv = leftAdjointMap adj e.inv :=
  leftAdjointMapIsoOf_inv (inferInstance : MonoidalClosed C) adj e

/-- The canonical left-adjoint isomorphism induced by an identity parameter is the identity. -/
@[simp]
theorem leftAdjointMapIso_refl
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) (L : C) :
    leftAdjointMapIso adj (Iso.refl L) = Iso.refl _ :=
  leftAdjointMapIsoOf_refl (inferInstance : MonoidalClosed C) adj L

/-- Canonical left-adjoint isomorphisms compose in the parameter. -/
theorem leftAdjointMapIso_trans
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L)
    {L₁ L₂ L₃ : C} (e₁ : L₁ ≅ L₂) (e₂ : L₂ ≅ L₃) :
    leftAdjointMapIso adj (e₁ ≪≫ e₂) =
      leftAdjointMapIso adj e₁ ≪≫ leftAdjointMapIso adj e₂ :=
  leftAdjointMapIsoOf_trans (inferInstance : MonoidalClosed C) adj e₁ e₂

/-- The canonical generated functor maps a parameter isomorphism to its mate isomorphism. -/
@[simp]
theorem leftAdjointFunctor_mapIso
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {T : C → C ⥤ C} (adj : ∀ L, T L ⊣ ihom L) {L₁ L₂ : C} (e : L₁ ≅ L₂) :
    (leftAdjointFunctor adj).mapIso e = leftAdjointMapIso adj e :=
  leftAdjointFunctorOf_mapIso (inferInstance : MonoidalClosed C) adj e

end CategoryTheory.MonoidalClosed
