/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineEtaleOver
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-! # Affine étale comparison for formal algebraic spaces -/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]

/-- The domain of an affine étale slice object is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_affineEtaleOver (U : AffineEtaleOver X) :
    IsFormalAlgebraicSpace U.obj.left := sorry

/-- An affine formal domain in the étale slice is a formal domain. -/
theorem isAffineFormalDomain_le_isFormalDomain :
    isAffineFormalDomain X ≤ isFormalDomain X := by
  intro U hU
  exact instIsFormalAlgebraicSpace_affineEtaleOver (X := X) ⟨U, hU⟩

/-- Forgetting the affine condition includes the affine formal étale slice in the formal
étale slice. -/
def affineEtaleOverForget : AffineEtaleOver X ⥤ EtaleOver X :=
  ιOfLE isAffineFormalDomain_le_isFormalDomain

/-- Forgetting affinity retains the underlying étale slice object. -/
@[simp]
theorem affineEtaleOverForget_obj (U : AffineEtaleOver X) :
    (affineEtaleOverForget.obj U).obj = U.obj := by rfl

namespace ReductionData

variable (R : ReductionData X)

/-- The affine scheme representing reduction pullback is the selected reduction of a stage
of the affine domain presentation. -/
def fibreAffineScheme (R : ReductionData X) (U : AffineEtaleOver X) : Over S :=
  AffineReduction.scheme U.property

/-- The selected affine fibre scheme is reduced in the étale-local sense. -/
private theorem fibreAffineScheme_reduced (U : AffineEtaleOver X) :
    AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u})
      (AlgebraicSpace.ofOver (fibreAffineScheme R U)) :=
  ⟨fibreAffineScheme R U, 𝟙 _, AlgebraicSpace.ofOver_id_presheaf_etale _,
    AlgebraicSpace.ofOver_id_locallySurjective _, AffineReduction.scheme_isReduced U.property⟩

/-- The structural map of the affine fibre scheme is the canonical factorization of its
domain-reduction inclusion through the specified reduction. -/
def fibreAffineSchemeHom (U : AffineEtaleOver X) :
    AlgebraicSpace.ofOver (fibreAffineScheme R U) ⟶ R.space :=
  R.mapFromReduced (fibreAffineScheme_reduced R U)
    (AffineReduction.ι U.property ≫ U.obj.hom)

/-- The affine fibre scheme maps to the reduction pullback by its two concrete projections. -/
private def fibreAffineSchemeIsoHom (U : AffineEtaleOver X) :
    yoneda.obj (fibreAffineScheme R U) ⟶ pullback R.ι U.obj.hom :=
  pullback.lift (fibreAffineSchemeHom R U) (AffineReduction.ι U.property)
    (R.mapFromReduced_spec (fibreAffineScheme_reduced R U)
      (AffineReduction.ι U.property ≫ U.obj.hom)).1

/-- The reduction pullback maps to the fixed affine reduction by reduced-source lifting. -/
private def fibreAffineSchemeIsoInv (U : AffineEtaleOver X) :
    pullback R.ι U.obj.hom ⟶ yoneda.obj (fibreAffineScheme R U) :=
  AffineReduction.lift U.property
    (etalePullback (X := U.obj.left) (Y := X) U.obj.hom (hf := U.obj.prop) R.space R.ι)
    (@etalePullback_isReduced S U.obj.left X inferInstance inferInstance
      U.obj.hom U.obj.prop R.space R.ι R.isReduced)
    (pullback.snd R.ι U.obj.hom)

/-- The concrete map to the reduction pullback followed by the lift back is the identity. -/
private theorem fibreAffineSchemeIso_hom_inv_id (U : AffineEtaleOver X) :
    fibreAffineSchemeIsoHom R U ≫ fibreAffineSchemeIsoInv R U =
      𝟙 (yoneda.obj (fibreAffineScheme R U)) := sorry

/-- The lift from the reduction pullback followed by its concrete representing map is the
identity. -/
private theorem fibreAffineSchemeIso_inv_hom_id (U : AffineEtaleOver X) :
    fibreAffineSchemeIsoInv R U ≫ fibreAffineSchemeIsoHom R U =
      𝟙 (pullback R.ι U.obj.hom) := sorry

/-- The selected affine reduction of the domain represents its pullback along the specified
reduction inclusion. -/
def fibreAffineSchemeIso (U : AffineEtaleOver X) :
    yoneda.obj (fibreAffineScheme R U) ≅ pullback R.ι U.obj.hom where
  hom := fibreAffineSchemeIsoHom R U
  inv := fibreAffineSchemeIsoInv R U
  hom_inv_id := fibreAffineSchemeIso_hom_inv_id R U
  inv_hom_id := fibreAffineSchemeIso_inv_hom_id R U

/-- Pullback of an affine formal étale domain to the reduction is representable by a scheme. -/
theorem pullbackReductionRepresentable (U : AffineEtaleOver X) :
    (pullback R.ι U.obj.hom).IsRepresentable :=
  CategoryTheory.Functor.IsRepresentable.mk' (fibreAffineSchemeIso R U)

/-- Any other representing scheme of the same reduction pullback is isomorphic to the
selected affine fibre scheme. -/
theorem fibreAffineScheme_unique (U : AffineEtaleOver X) {T : Over S}
    (e : yoneda.obj T ≅ pullback R.ι U.obj.hom) :
    Nonempty (T ≅ fibreAffineScheme R U) :=
  ⟨CategoryTheory.Yoneda.fullyFaithful.preimageIso
    (e ≪≫ (fibreAffineSchemeIso R U).symm)⟩

/-- The selected representing scheme of reduction pullback is affine. -/
theorem fibreAffineScheme_isAffine (U : AffineEtaleOver X) :
    IsAffine (fibreAffineScheme R U).left :=
  AffineReduction.scheme_isAffine U.property

/-- The represented affine fibre and the algebraic-space reduction pullback are isomorphic. -/
def fibreToReductionAlong (U : AffineEtaleOver X) :
    AlgebraicSpace.ofOver (fibreAffineScheme R U) ≅
      ((toSpacesEtale R).obj (affineEtaleOverForget.obj U)).left where
  hom := (fibreAffineSchemeIso R U).hom
  inv := (fibreAffineSchemeIso R U).inv
  hom_inv_id := (fibreAffineSchemeIso R U).hom_inv_id
  inv_hom_id := (fibreAffineSchemeIso R U).inv_hom_id

/-- The structural morphism of the fixed affine fibre scheme is étale over the reduction. -/
theorem fibreAffineSchemeHom_etale (U : AffineEtaleOver X) :
    AlgebraicSpace.Etale (fibreAffineSchemeHom R U) := sorry

/-- An affine étale slice arrow commutes with the structural maps into the formal space. -/
private theorem toAffineEtale_map_w {U V : AffineEtaleOver X} (f : U ⟶ V) :
    U.obj.hom ≫ 𝟙 X = f.hom.left ≫ V.obj.hom := by
  exact f.hom.w.symm

/-- An arrow between affine formal domains induces the actual Yoneda preimage of the
corresponding arrow of reduction pullbacks. -/
def fibreAffineSchemeMap {U V : AffineEtaleOver X} (f : U ⟶ V) :
    fibreAffineScheme R U ⟶ fibreAffineScheme R V :=
  CategoryTheory.Yoneda.fullyFaithful.preimage
    ((fibreAffineSchemeIso R U).hom ≫
      pullback.map R.ι U.obj.hom R.ι V.obj.hom (𝟙 _) f.hom.left (𝟙 _)
        (by simp) (toAffineEtale_map_w f) ≫ (fibreAffineSchemeIso R V).inv)

/-- The induced arrow of affine fibre schemes commutes with their maps to the reduction. -/
private theorem toAffineEtale_homMk_w {U V : AffineEtaleOver X} (f : U ⟶ V) :
    AlgebraicSpace.ofOverMap (fibreAffineSchemeMap R f) ≫ fibreAffineSchemeHom R V =
      fibreAffineSchemeHom R U := sorry

/-- Reduction pullback sends an affine formal étale domain to its concrete affine chart. -/
private def toAffineEtaleObj (U : AffineEtaleOver X) :
    AlgebraicSpace.affineEtaleSite R.space :=
  @AlgebraicSpace.affineEtaleSite.mk S R.space (fibreAffineScheme R U)
    (fibreAffineScheme_isAffine R U) (fibreAffineSchemeHom R U)
    (fibreAffineSchemeHom_etale R U)

/-- Reduction pullback sends an affine formal étale arrow to the induced scheme arrow. -/
private def toAffineEtaleMap {U V : AffineEtaleOver X} (f : U ⟶ V) :
    toAffineEtaleObj R U ⟶ toAffineEtaleObj R V :=
  homMk (MorphismProperty.CostructuredArrow.homMk (fibreAffineSchemeMap R f) trivial
    (toAffineEtale_homMk_w R f))

/-- Reduction pullback preserves identity arrows on affine formal étale domains. -/
private theorem toAffineEtale_map_id (U : AffineEtaleOver X) :
    toAffineEtaleMap R (𝟙 U) = 𝟙 (toAffineEtaleObj R U) := sorry

/-- Reduction pullback preserves composition of affine formal étale arrows. -/
private theorem toAffineEtale_map_comp {U V W : AffineEtaleOver X}
    (f : U ⟶ V) (g : V ⟶ W) :
    toAffineEtaleMap R (f ≫ g) = toAffineEtaleMap R f ≫ toAffineEtaleMap R g := sorry

/-- The forward affine étale comparison takes the affine scheme representing reduction
pullback and its canonical map to the reduction. -/
@[expose] def toAffineEtale : AffineEtaleOver X ⥤ AlgebraicSpace.affineEtaleSite R.space where
  obj U := @AlgebraicSpace.affineEtaleSite.mk S R.space (fibreAffineScheme R U)
    (fibreAffineScheme_isAffine R U) (fibreAffineSchemeHom R U)
    (fibreAffineSchemeHom_etale R U)
  map f := homMk (MorphismProperty.CostructuredArrow.homMk (fibreAffineSchemeMap R f)
    trivial (by exact toAffineEtale_homMk_w R f))
  map_id U := by exact toAffineEtale_map_id R U
  map_comp f g := by exact toAffineEtale_map_comp R f g

/-- The forward affine comparison uses the selected stage-reduction scheme. -/
@[simp]
theorem toAffineEtale_obj_left (U : AffineEtaleOver X) :
    ((toAffineEtale R).obj U).obj.left = fibreAffineScheme R U := by rfl

/-- The forward affine comparison has the canonical structural map to the reduction. -/
@[simp]
theorem toAffineEtale_obj_hom (U : AffineEtaleOver X) :
    ((toAffineEtale R).obj U).obj.hom = fibreAffineSchemeHom R U := by rfl

/-- The inverse representing isomorphism commutes with the maps to the reduction. -/
private theorem toSpacesIsoToAffine_w (U : AffineEtaleOver X) :
    (fibreToReductionAlong R U).inv ≫ fibreAffineSchemeHom R U =
      ((toSpacesEtale R).obj (affineEtaleOverForget.obj U)).hom := sorry

/-- The algebraic-space and affine-scheme descriptions of reduction pullback agree in the
spaces étale slice. -/
def toSpacesIsoToAffine (U : AffineEtaleOver X) :
    (toSpacesEtale R).obj (affineEtaleOverForget.obj U) ≅
      (AlgebraicSpace.affineEtaleToSpaces R.space).obj ((toAffineEtale R).obj U) :=
  MorphismProperty.Over.isoMk (fibreToReductionAlong R U).symm (toSpacesIsoToAffine_w R U)

/-- The two descriptions of reduction pullback commute with affine étale arrows. -/
private theorem affineEtaleOverForget_comp_toSpacesEtale_naturality
    {U V : AffineEtaleOver X} (f : U ⟶ V) :
    (affineEtaleOverForget ⋙ toSpacesEtale R).map f ≫ (toSpacesIsoToAffine R V).hom =
      (toSpacesIsoToAffine R U).hom ≫
        (toAffineEtale R ⋙ AlgebraicSpace.affineEtaleToSpaces R.space).map f := sorry

/-- The forward affine comparison agrees naturally with the general formal étale comparison
after forgetting affinity. -/
def affineEtaleOverForget_comp_toSpacesEtale :
    affineEtaleOverForget ⋙ toSpacesEtale R ≅
      toAffineEtale R ⋙ AlgebraicSpace.affineEtaleToSpaces R.space :=
  NatIso.ofComponents (toSpacesIsoToAffine R)
    (affineEtaleOverForget_comp_toSpacesEtale_naturality R)

/-- The fixed extension of an affine étale chart over the reduction admits a directed affine
thickening presentation with index in the same universe. -/
theorem exists_isDirectedAffineThickeningColimit_ofAffineEtale
    (V : AlgebraicSpace.affineEtaleSite R.space) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D
        (extensionAlong R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V)) := sorry

/-- The inverse affine comparison is the existing extension functor lifted to affine formal
domains. -/
@[expose] def ofAffineEtale : AlgebraicSpace.affineEtaleSite R.space ⥤ AffineEtaleOver X :=
  (isAffineFormalDomain X).lift
    (AlgebraicSpace.affineEtaleToSpaces R.space ⋙ ofSpacesEtale R ⋙ (isFormalDomain X).ι)
    (exists_isDirectedAffineThickeningColimit_ofAffineEtale R)

/-- The inverse affine comparison retains the concrete extension presheaf. -/
@[simp]
theorem ofAffineEtale_obj_left (V : AlgebraicSpace.affineEtaleSite R.space) :
    ((ofAffineEtale R).obj V).obj.left =
      extensionAlong R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V) := by rfl

/-- The inverse affine comparison retains the concrete extension projection. -/
@[simp]
theorem ofAffineEtale_obj_hom (V : AlgebraicSpace.affineEtaleSite R.space) :
    ((ofAffineEtale R).obj V).obj.hom =
      extensionHom R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V) := by rfl

/-- Forgetting affinity on the inverse comparison recovers the general extension functor. -/
def ofAffineEtale_comp_forget :
    ofAffineEtale R ⋙ affineEtaleOverForget ≅
      AlgebraicSpace.affineEtaleToSpaces R.space ⋙ ofSpacesEtale R := Iso.refl _

/-- The affine unit map is the general unit transported through the concrete fibre
comparison. -/
def affineEtaleUnitHom (U : AffineEtaleOver X) :
    U.obj.left ⟶ ((ofAffineEtale R).obj ((toAffineEtale R).obj U)).obj.left :=
  unitHom R (affineEtaleOverForget.obj U) ≫
    extensionAlongMap R (toSpacesIsoToAffine R U).hom

/-- The inverse affine unit map is the inverse general unit transported through the fibre
comparison. -/
def affineEtaleUnitInv (U : AffineEtaleOver X) :
    ((ofAffineEtale R).obj ((toAffineEtale R).obj U)).obj.left ⟶ U.obj.left :=
  extensionAlongMap R (toSpacesIsoToAffine R U).inv ≫
    unitInv R (affineEtaleOverForget.obj U)

/-- The affine unit map commutes with the structural morphism to the formal space. -/
private theorem affineEtaleUnitIsoApp_hom_w (U : AffineEtaleOver X) :
    affineEtaleUnitHom R U ≫
      ((ofAffineEtale R).obj ((toAffineEtale R).obj U)).obj.hom = U.obj.hom := sorry

/-- The inverse affine unit map commutes with the structural morphism to the formal space. -/
private theorem affineEtaleUnitIsoApp_inv_w (U : AffineEtaleOver X) :
    affineEtaleUnitInv R U ≫ U.obj.hom =
      ((ofAffineEtale R).obj ((toAffineEtale R).obj U)).obj.hom := sorry

/-- The affine unit and inverse unit compose to the identity on the original object. -/
private theorem affineEtaleUnitIsoApp_hom_inv_id (U : AffineEtaleOver X) :
    (homMk (MorphismProperty.Over.homMk (affineEtaleUnitHom R U)
      (affineEtaleUnitIsoApp_hom_w R U) trivial) :
        U ⟶ (ofAffineEtale R).obj ((toAffineEtale R).obj U)) ≫
      homMk (MorphismProperty.Over.homMk (affineEtaleUnitInv R U)
        (affineEtaleUnitIsoApp_inv_w R U) trivial) = 𝟙 U := sorry

/-- The inverse affine unit and affine unit compose to the identity on the extended object. -/
private theorem affineEtaleUnitIsoApp_inv_hom_id (U : AffineEtaleOver X) :
    (homMk (MorphismProperty.Over.homMk (affineEtaleUnitInv R U)
      (affineEtaleUnitIsoApp_inv_w R U) trivial) :
        (ofAffineEtale R).obj ((toAffineEtale R).obj U) ⟶ U) ≫
      homMk (MorphismProperty.Over.homMk (affineEtaleUnitHom R U)
        (affineEtaleUnitIsoApp_hom_w R U) trivial) =
          𝟙 ((ofAffineEtale R).obj ((toAffineEtale R).obj U)) := sorry

/-- The concrete affine unit and its inverse define an isomorphism of affine formal étale
domains. -/
def affineEtaleUnitIsoApp (U : AffineEtaleOver X) :
    U ≅ (ofAffineEtale R).obj ((toAffineEtale R).obj U) where
  hom := homMk (MorphismProperty.Over.homMk (affineEtaleUnitHom R U)
    (affineEtaleUnitIsoApp_hom_w R U) trivial)
  inv := homMk (MorphismProperty.Over.homMk (affineEtaleUnitInv R U)
    (affineEtaleUnitIsoApp_inv_w R U) trivial)
  hom_inv_id := affineEtaleUnitIsoApp_hom_inv_id R U
  inv_hom_id := affineEtaleUnitIsoApp_inv_hom_id R U

/-- The affine unit isomorphisms are natural in affine formal étale domains. -/
private theorem affineEtaleUnitIso_naturality {U V : AffineEtaleOver X} (f : U ⟶ V) :
    f ≫ (affineEtaleUnitIsoApp R V).hom =
      (affineEtaleUnitIsoApp R U).hom ≫ (toAffineEtale R ⋙ ofAffineEtale R).map f := sorry

/-- The identity on affine formal étale domains is naturally isomorphic to reduction followed
by extension. -/
def affineEtaleUnitIso : 𝟭 (AffineEtaleOver X) ≅ toAffineEtale R ⋙ ofAffineEtale R :=
  NatIso.ofComponents (affineEtaleUnitIsoApp R) (affineEtaleUnitIso_naturality R)

/-- The general counit identifies the represented affine fibre of an extension with its
original affine chart at the level of presheaves. -/
private def affineEtaleCounitPresheafIso (V : AlgebraicSpace.affineEtaleSite R.space) :
    yoneda.obj (fibreAffineScheme R ((ofAffineEtale R).obj V)) ≅ yoneda.obj V.obj.left where
  hom := (fibreToReductionAlong R ((ofAffineEtale R).obj V)).hom ≫
    counitHom R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V)
  inv := counitInv R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V) ≫
    (fibreToReductionAlong R ((ofAffineEtale R).obj V)).inv
  hom_inv_id :=
    ((fibreToReductionAlong R ((ofAffineEtale R).obj V)) ≪≫
      counitSpaceIso R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V)).hom_inv_id
  inv_hom_id :=
    ((fibreToReductionAlong R ((ofAffineEtale R).obj V)) ≪≫
      counitSpaceIso R ((AlgebraicSpace.affineEtaleToSpaces R.space).obj V)).inv_hom_id

/-- The counit scheme map is the actual Yoneda preimage of the transported general counit. -/
def affineEtaleCounitSchemeHom (V : AlgebraicSpace.affineEtaleSite R.space) :
    fibreAffineScheme R ((ofAffineEtale R).obj V) ⟶ V.obj.left :=
  CategoryTheory.Yoneda.fullyFaithful.preimage (affineEtaleCounitPresheafIso R V).hom

/-- The inverse counit scheme map is the actual Yoneda preimage of the transported inverse
general counit. -/
def affineEtaleCounitSchemeInv (V : AlgebraicSpace.affineEtaleSite R.space) :
    V.obj.left ⟶ fibreAffineScheme R ((ofAffineEtale R).obj V) :=
  CategoryTheory.Yoneda.fullyFaithful.preimage (affineEtaleCounitPresheafIso R V).inv

/-- The scheme counit is the fully faithful Yoneda preimage of the general counit
isomorphism. -/
def affineEtaleCounitSchemeIso (V : AlgebraicSpace.affineEtaleSite R.space) :
    fibreAffineScheme R ((ofAffineEtale R).obj V) ≅ V.obj.left :=
  CategoryTheory.Yoneda.fullyFaithful.preimageIso (affineEtaleCounitPresheafIso R V)

/-- The scheme counit isomorphism has the specified Yoneda-preimage forward map. -/
@[simp]
theorem affineEtaleCounitSchemeIso_hom (V : AlgebraicSpace.affineEtaleSite R.space) :
    (affineEtaleCounitSchemeIso R V).hom = affineEtaleCounitSchemeHom R V := by rfl

/-- The scheme counit map commutes with the structural map to the reduction. -/
private theorem affineEtaleCounitIsoApp_w (V : AlgebraicSpace.affineEtaleSite R.space) :
    AlgebraicSpace.ofOverMap (affineEtaleCounitSchemeIso R V).hom ≫ V.obj.hom =
      fibreAffineSchemeHom R ((ofAffineEtale R).obj V) := sorry

/-- The concrete scheme counit lifts to an isomorphism of affine étale charts. -/
def affineEtaleCounitIsoApp (V : AlgebraicSpace.affineEtaleSite R.space) :
    (toAffineEtale R).obj ((ofAffineEtale R).obj V) ≅ V :=
  ObjectProperty.isoMk _
    (MorphismProperty.CostructuredArrow.isoMk (affineEtaleCounitSchemeIso R V)
      trivial trivial (affineEtaleCounitIsoApp_w R V))

/-- The affine counit isomorphisms are natural in affine étale charts. -/
private theorem affineEtaleCounitIso_naturality
    {V W : AlgebraicSpace.affineEtaleSite R.space} (f : V ⟶ W) :
    (ofAffineEtale R ⋙ toAffineEtale R).map f ≫ (affineEtaleCounitIsoApp R W).hom =
      (affineEtaleCounitIsoApp R V).hom ≫ f := sorry

/-- Extension followed by reduction is naturally isomorphic to the identity on affine
étale charts. -/
def affineEtaleCounitIso :
    ofAffineEtale R ⋙ toAffineEtale R ≅ 𝟭 (AlgebraicSpace.affineEtaleSite R.space) :=
  NatIso.ofComponents (affineEtaleCounitIsoApp R) (affineEtaleCounitIso_naturality R)

/-- Affine formal étale domains over a formal algebraic space are equivalent to affine
étale charts of its specified reduction. -/
@[expose] def affineEtaleEquiv : AffineEtaleOver X ≌ AlgebraicSpace.affineEtaleSite R.space :=
  CategoryTheory.Equivalence.mk (toAffineEtale R) (ofAffineEtale R)
    (affineEtaleUnitIso R) (affineEtaleCounitIso R)

/-- The affine étale equivalence uses reduction pullback as its forward functor. -/
@[simp]
theorem affineEtaleEquiv_functor :
    (affineEtaleEquiv R).functor = toAffineEtale R :=
  rfl

/-- The affine étale equivalence uses the fixed extension construction as its inverse
functor. -/
@[simp]
theorem affineEtaleEquiv_inverse :
    (affineEtaleEquiv R).inverse = ofAffineEtale R :=
  rfl

/-- Affine formal étale domains over an affine formal algebraic space are equivalent to
affine étale charts of its specified reduction. -/
def affineEtaleOverEquiv (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    (R : ReductionData X)
    (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X) :
    AffineEtaleOver X ≌ AlgebraicSpace.affineEtaleSite R.space :=
  let _ := hX
  affineEtaleEquiv R

/-- The equivalence from affine formal étale domains uses reduction pullback as its forward
functor. -/
@[simp]
theorem affineEtaleOverEquiv_functor
    (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X) :
    (affineEtaleOverEquiv X R hX).functor = toAffineEtale R := by rfl

/-- The equivalence from affine formal étale domains uses the fixed extension construction
as its inverse functor. -/
@[simp]
theorem affineEtaleOverEquiv_inverse
    (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X) :
    (affineEtaleOverEquiv X R hX).inverse = ofAffineEtale R := by rfl

end ReductionData

end AlgebraicGeometry.FormalAlgebraicSpace
