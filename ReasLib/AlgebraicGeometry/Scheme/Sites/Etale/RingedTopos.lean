/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose

/-!
# The small-to-big étale morphism of ringed topoi

This module equips étale relocalization with its canonical map on structure sheaves and
constructs the resulting morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

universe u

variable {S T : Scheme.{u}}

/-- The realization of a small étale object is canonically unchanged when it is viewed over
`S` by relocalization along `f`. -/
noncomputable def realizationIso (f : T ⟶ S) :
    Scheme.smallEtaleToScheme T ≅ relocalizationFunctor f ⋙ Over.forget S :=
  Functor.isoWhiskerLeft (MorphismProperty.Over.forget @Etale ⊤ T)
    (Over.mapForget f).symm

/-- Inverse image along étale relocalization carries the big structure sheaf to the small
structure sheaf by the canonical identification of source schemes. -/
noncomputable def inverseImageStructureMap (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
      T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
        (StandardTopology.Big.structureSheaf .etale S) ⟶
      Small.structureSheaf T :=
  Scheme.Site.inverseStructureSheafMap T.smallEtaleTopology
    (StandardTopology.etale.overTopology S) (Scheme.smallEtaleToScheme T)
    (Over.forget S) (relocalizationFunctor f) (realizationIso f).hom
    (Small.structurePresheaf_isSheaf T)
    (StandardTopology.Big.structurePresheaf_isSheaf .etale S)

/-- Objectwise, the étale inverse-image structure map is pullback on global sections. -/
theorem inverseImageStructureMap_app (f : T ⟶ S) (U : T.Etaleᵒᵖ) :
    (inverseImageStructureMap f).hom.app U =
      RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom := sorry

/-- The reverse map for the étale inverse-image structure comparison. -/
noncomputable def inverseImageStructureMapInv (f : T ⟶ S) :
    Small.structureSheaf T ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
          (StandardTopology.Big.structureSheaf .etale S) :=
  Scheme.Site.structureSheafMap T.smallEtaleTopology
    (StandardTopology.etale.overTopology S) (Scheme.smallEtaleToScheme T)
    (Over.forget S) (relocalizationFunctor f) (realizationIso f).inv
    (Small.structurePresheaf_isSheaf T)
    (StandardTopology.Big.structurePresheaf_isSheaf .etale S)

/-- The two étale comparison maps compose to the inverse-image identity. -/
theorem inverseImageStructureMap_homInvId (f : T ⟶ S) :
    inverseImageStructureMap f ≫ inverseImageStructureMapInv f =
      𝟙 (((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
          (StandardTopology.Big.structureSheaf .etale S)) := sorry

/-- The two étale comparison maps compose to the small structure-sheaf identity. -/
theorem inverseImageStructureMap_invHomId (f : T ⟶ S) :
    inverseImageStructureMapInv f ≫ inverseImageStructureMap f =
      𝟙 (Small.structureSheaf T) := sorry

/-- The unlifted identification `i_f⁻¹𝒪 ≅ 𝒪` for small-to-big étale relocalization. -/
noncomputable def presentedInverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
      T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
        (StandardTopology.Big.structureSheaf .etale S) ≅
      Small.structureSheaf T where
  hom := inverseImageStructureMap f
  inv := inverseImageStructureMapInv f
  hom_inv_id := inverseImageStructureMap_homInvId f
  inv_hom_id := inverseImageStructureMap_invHomId f

/-- Objectwise, the unlifted étale inverse-image isomorphism is pullback on global sections. -/
theorem presentedInverseImageStructureIso_hom_app (f : T ⟶ S) (U : T.Etaleᵒᵖ) :
    (presentedInverseImageStructureIso f).hom.hom.app U =
      RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom := sorry

/-- The unlifted étale inverse-image structure map is an isomorphism. -/
instance presentedInverseImageStructureIso_hom_isIso (f : T ⟶ S) :
    IsIso (presentedInverseImageStructureIso f).hom := sorry

/-- The canonical identification `i_f⁻¹𝒪 ≅ 𝒪` after lifting section rings to the site
universe. -/
noncomputable def presentedLiftedInverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u + 1}
      T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
        (StandardTopology.Big.liftedStructureSheaf .etale S) ≅
      Small.liftedStructureSheaf T :=
  (sheafCompose T.smallEtaleTopology
    (Scheme.Site.ringUniverseLift.{u, u + 1})).mapIso
      (presentedInverseImageStructureIso f)

/-- Objectwise, the lifted étale inverse-image isomorphism is the universe lift of pullback on
global sections. -/
theorem presentedLiftedInverseImageStructureIso_hom_app
    (f : T ⟶ S) (U : T.Etaleᵒᵖ) :
    (presentedLiftedInverseImageStructureIso f).hom.hom.app U =
      (Scheme.Site.ringUniverseLift.{u, u + 1}).map
        (RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom) := sorry

/-- The canonical lifted étale inverse-image structure map is an isomorphism. -/
instance presentedLiftedInverseImageStructureIso_hom_isIso (f : T ⟶ S) :
    IsIso (presentedLiftedInverseImageStructureIso f).hom := sorry

/-- The ring-valued direct image presented by small-to-big étale relocalization. -/
noncomputable def ringDirectImage (f : T ⟶ S) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} ⥤
      Sheaf (StandardTopology.etale.overTopology S) RingCat.{u + 1} :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous RingCat.{u + 1}
    T.smallEtaleTopology (StandardTopology.etale.overTopology S)

/-- The étale ring-valued direct image is the cocontinuous sheaf direct image. -/
theorem ringDirectImage_def (f : T ⟶ S) :
    ringDirectImage f =
      (relocalizationFunctor f).sheafPushforwardCocontinuous RingCat.{u + 1}
        T.smallEtaleTopology (StandardTopology.etale.overTopology S) := sorry

/-- Forgetting rings commutes with the presented étale direct image. -/
noncomputable def ringDirectImageForgetIso (f : T ⟶ S) :
    ringDirectImage f ⋙
        sheafCompose (StandardTopology.etale.overTopology S)
          (CategoryTheory.forget RingCat.{u + 1}) ≅
      sheafCompose T.smallEtaleTopology
          (CategoryTheory.forget RingCat.{u + 1}) ⋙
        (morphismOfTopoi f).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
      (relocalizationFunctor f)
      (CategoryTheory.forget RingCat.{u + 1}) T.smallEtaleTopology
      (StandardTopology.etale.overTopology S) ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose T.smallEtaleTopology (CategoryTheory.forget RingCat.{u + 1}))
      (eqToIso (morphismOfTopoi_pushforward f).symm)

/-- The direct-image form of the étale structure-sheaf map. -/
noncomputable def directStructureMap (f : T ⟶ S) :
    StandardTopology.Big.liftedStructureSheaf .etale S ⟶
      (ringDirectImage f).obj (Small.liftedStructureSheaf T) :=
  ((relocalizationFunctor f).sheafAdjunctionCocontinuous RingCat.{u + 1}
    T.smallEtaleTopology (StandardTopology.etale.overTopology S)).homEquiv _ _
      (presentedLiftedInverseImageStructureIso f).hom

/-- The étale direct-image structure map preserves the canonical internal-ring operations. -/
theorem directStructureMap_isRingCompatible (f : T ⟶ S) :
    RingedSite.ToposHom.Direct.IsRingCompatible
      (X := Small.liftedRingedSite T)
      (Y := StandardTopology.Big.liftedRingedSite .etale S) (morphismOfTopoi f)
      (ringDirectImage f) (ringDirectImageForgetIso f) (directStructureMap f) := sorry

/-- The canonical small-to-big étale morphism of ringed topoi. -/
noncomputable def ringedToposHom (f : T ⟶ S) :
    RingedSite.ToposHom (Small.liftedRingedSite T)
      (StandardTopology.Big.liftedRingedSite .etale S) :=
  RingedSite.ToposHom.ofDirectImage
    (X := Small.liftedRingedSite T)
    (Y := StandardTopology.Big.liftedRingedSite .etale S)
    (morphismOfTopoi f) (ringDirectImage f)
    (ringDirectImageForgetIso f) (directStructureMap f)
    (directStructureMap_isRingCompatible f)

/-- The underlying topos morphism of the small-to-big étale ringed morphism is the
relocalization morphism. -/
theorem ringedToposHom_toTopos (f : T ⟶ S) :
    (ringedToposHom f).toTopos = morphismOfTopoi f := sorry

/-- The inverse-image structure map of the small-to-big étale ringed morphism is an
isomorphism. -/
instance ringedToposHom_structureMap_isIso (f : T ⟶ S) :
    IsIso (ringedToposHom f).structureMap := sorry

/-- The canonical inverse-image identification for small-to-big étale relocalization. -/
noncomputable def inverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u + 1}
      T.smallEtaleTopology (StandardTopology.etale.overTopology S)).obj
        (StandardTopology.Big.liftedStructureSheaf .etale S) ≅
      Small.liftedStructureSheaf T :=
  presentedLiftedInverseImageStructureIso f

/-- The hom component of the canonical étale inverse-image structure isomorphism is the
structure map of `ringedToposHom f`. -/
theorem inverseImageStructureIso_hom_app (f : T ⟶ S) (U : T.Etaleᵒᵖ) :
    (inverseImageStructureIso f).hom.hom.app U =
      (Scheme.Site.ringUniverseLift.{u, u + 1}).map
        (RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom) := sorry
end AlgebraicGeometry.Scheme.Etale.SmallToBig
