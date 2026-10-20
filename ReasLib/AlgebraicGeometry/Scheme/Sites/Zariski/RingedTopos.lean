/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose

/-!
# The small-to-big Zariski morphism of ringed topoi

This module equips Zariski relocalization with its canonical map on structure sheaves and
constructs the resulting morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.Scheme.Zariski.SmallToBig

universe u

variable {S T : Scheme.{u}}

/-- The realization of a small Zariski object is canonically unchanged when it is viewed over
`S` by relocalization along `f`. -/
noncomputable def realizationIso (f : T ⟶ S) :
    Scheme.smallZariskiToScheme T ≅ relocalizationFunctor f ⋙ Over.forget S :=
  Functor.isoWhiskerLeft (Scheme.smallZariskiForget T) (Over.mapForget f).symm

/-- Inverse image along Zariski relocalization carries the big structure sheaf to the small
structure sheaf by the canonical identification of source schemes. -/
noncomputable def inverseImageStructureMap (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
      T.smallZariskiTopology S.bigZariskiTopology).obj
        (StandardTopology.Big.structureSheaf .zariski S) ⟶
      Small.structureSheaf T :=
  Scheme.Site.inverseStructureSheafMap T.smallZariskiTopology S.bigZariskiTopology
    (Scheme.smallZariskiToScheme T) (Over.forget S) (relocalizationFunctor f)
    (realizationIso f).hom (Small.structurePresheaf_isSheaf T)
    (StandardTopology.Big.structurePresheaf_isSheaf .zariski S)

/-- Objectwise, the Zariski inverse-image structure map is pullback on global sections. -/
theorem inverseImageStructureMap_app (f : T ⟶ S) (U : T.smallZariskiSiteᵒᵖ) :
    (inverseImageStructureMap f).hom.app U =
      RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom := sorry

/-- The reverse map for the Zariski inverse-image structure comparison. -/
noncomputable def inverseImageStructureMapInv (f : T ⟶ S) :
    Small.structureSheaf T ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        T.smallZariskiTopology S.bigZariskiTopology).obj
          (StandardTopology.Big.structureSheaf .zariski S) :=
  Scheme.Site.structureSheafMap T.smallZariskiTopology S.bigZariskiTopology
    (Scheme.smallZariskiToScheme T) (Over.forget S) (relocalizationFunctor f)
    (realizationIso f).inv (Small.structurePresheaf_isSheaf T)
    (StandardTopology.Big.structurePresheaf_isSheaf .zariski S)

/-- The two Zariski comparison maps compose to the inverse-image identity. -/
theorem inverseImageStructureMap_homInvId (f : T ⟶ S) :
    inverseImageStructureMap f ≫ inverseImageStructureMapInv f =
      𝟙 (((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        T.smallZariskiTopology S.bigZariskiTopology).obj
          (StandardTopology.Big.structureSheaf .zariski S)) := sorry

/-- The two Zariski comparison maps compose to the small structure-sheaf identity. -/
theorem inverseImageStructureMap_invHomId (f : T ⟶ S) :
    inverseImageStructureMapInv f ≫ inverseImageStructureMap f =
      𝟙 (Small.structureSheaf T) := sorry

/-- The unlifted identification `i_f⁻¹𝒪 ≅ 𝒪` for small-to-big Zariski relocalization. -/
noncomputable def presentedInverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
      T.smallZariskiTopology S.bigZariskiTopology).obj
        (StandardTopology.Big.structureSheaf .zariski S) ≅
      Small.structureSheaf T where
  hom := inverseImageStructureMap f
  inv := inverseImageStructureMapInv f
  hom_inv_id := inverseImageStructureMap_homInvId f
  inv_hom_id := inverseImageStructureMap_invHomId f

/-- Objectwise, the unlifted Zariski inverse-image isomorphism is pullback on global sections. -/
theorem presentedInverseImageStructureIso_hom_app
    (f : T ⟶ S) (U : T.smallZariskiSiteᵒᵖ) :
    (presentedInverseImageStructureIso f).hom.hom.app U =
      RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom := sorry

/-- The unlifted Zariski inverse-image structure map is an isomorphism. -/
instance presentedInverseImageStructureIso_hom_isIso (f : T ⟶ S) :
    IsIso (presentedInverseImageStructureIso f).hom := sorry

/-- The site-presented identification `i_f⁻¹𝒪 ≅ 𝒪` after lifting section rings to the site
universe. -/
noncomputable def presentedLiftedInverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u + 1}
      T.smallZariskiTopology S.bigZariskiTopology).obj
        (StandardTopology.Big.liftedStructureSheaf .zariski S) ≅
      Small.liftedStructureSheaf T :=
  (sheafCompose T.smallZariskiTopology
    (Scheme.Site.ringUniverseLift.{u, u + 1})).mapIso
      (presentedInverseImageStructureIso f)

/-- Objectwise, the lifted Zariski inverse-image isomorphism is the universe lift of pullback
on global sections. -/
theorem presentedLiftedInverseImageStructureIso_hom_app
    (f : T ⟶ S) (U : T.smallZariskiSiteᵒᵖ) :
    (presentedLiftedInverseImageStructureIso f).hom.hom.app U =
      (Scheme.Site.ringUniverseLift.{u, u + 1}).map
        (RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom) := sorry

/-- The canonical lifted Zariski inverse-image structure map is an isomorphism. -/
instance presentedLiftedInverseImageStructureIso_hom_isIso (f : T ⟶ S) :
    IsIso (presentedLiftedInverseImageStructureIso f).hom := sorry

/-- The ring-valued direct image presented by small-to-big Zariski relocalization. -/
noncomputable def ringDirectImage (f : T ⟶ S) :
    Sheaf T.smallZariskiTopology RingCat.{u + 1} ⥤
      Sheaf S.bigZariskiTopology RingCat.{u + 1} :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous RingCat.{u + 1}
    T.smallZariskiTopology S.bigZariskiTopology

/-- The Zariski ring-valued direct image is the cocontinuous sheaf direct image. -/
theorem ringDirectImage_def (f : T ⟶ S) :
    ringDirectImage f =
      (relocalizationFunctor f).sheafPushforwardCocontinuous RingCat.{u + 1}
        T.smallZariskiTopology S.bigZariskiTopology := sorry

/-- Forgetting rings commutes with the presented Zariski direct image. -/
noncomputable def ringDirectImageForgetIso (f : T ⟶ S) :
    ringDirectImage f ⋙
        sheafCompose S.bigZariskiTopology
          (CategoryTheory.forget RingCat.{u + 1}) ≅
      sheafCompose T.smallZariskiTopology
          (CategoryTheory.forget RingCat.{u + 1}) ⋙
        (morphismOfTopoi f).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
      (relocalizationFunctor f)
      (CategoryTheory.forget RingCat.{u + 1}) T.smallZariskiTopology
      S.bigZariskiTopology ≪≫
    Functor.isoWhiskerLeft
      (sheafCompose T.smallZariskiTopology (CategoryTheory.forget RingCat.{u + 1}))
      (eqToIso (morphismOfTopoi_pushforward f).symm)

/-- The direct-image form of the Zariski structure-sheaf map. -/
noncomputable def directStructureMap (f : T ⟶ S) :
    StandardTopology.Big.liftedStructureSheaf .zariski S ⟶
      (ringDirectImage f).obj (Small.liftedStructureSheaf T) :=
  ((relocalizationFunctor f).sheafAdjunctionCocontinuous RingCat.{u + 1}
    T.smallZariskiTopology S.bigZariskiTopology).homEquiv _ _
      (presentedLiftedInverseImageStructureIso f).hom

/-- The Zariski direct-image structure map preserves the canonical internal-ring operations. -/
theorem directStructureMap_isRingCompatible (f : T ⟶ S) :
    RingedSite.ToposHom.Direct.IsRingCompatible
      (X := Small.liftedRingedSite T)
      (Y := StandardTopology.Big.liftedRingedSite .zariski S) (morphismOfTopoi f)
      (ringDirectImage f) (ringDirectImageForgetIso f) (directStructureMap f) := sorry

/-- The canonical small-to-big Zariski morphism of ringed topoi. -/
noncomputable def ringedToposHom (f : T ⟶ S) :
    RingedSite.ToposHom (Small.liftedRingedSite T)
      (StandardTopology.Big.liftedRingedSite .zariski S) :=
  RingedSite.ToposHom.ofDirectImage
    (X := Small.liftedRingedSite T)
    (Y := StandardTopology.Big.liftedRingedSite .zariski S)
    (morphismOfTopoi f) (ringDirectImage f)
    (ringDirectImageForgetIso f) (directStructureMap f)
    (directStructureMap_isRingCompatible f)

/-- The underlying topos morphism of the small-to-big Zariski ringed morphism is the
relocalization morphism. -/
theorem ringedToposHom_toTopos (f : T ⟶ S) :
    (ringedToposHom f).toTopos = morphismOfTopoi f := sorry

/-- The inverse-image structure map of the small-to-big Zariski ringed morphism is an
isomorphism. -/
instance ringedToposHom_structureMap_isIso (f : T ⟶ S) :
    IsIso (ringedToposHom f).structureMap := sorry

/-- The canonical inverse-image identification for small-to-big Zariski relocalization. -/
noncomputable def inverseImageStructureIso (f : T ⟶ S) :
    ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u + 1}
      T.smallZariskiTopology S.bigZariskiTopology).obj
        (StandardTopology.Big.liftedStructureSheaf .zariski S) ≅
      Small.liftedStructureSheaf T :=
  presentedLiftedInverseImageStructureIso f

/-- The hom component of the canonical Zariski inverse-image structure isomorphism is the
structure map of `ringedToposHom f`. -/
theorem inverseImageStructureIso_hom_app
    (f : T ⟶ S) (U : T.smallZariskiSiteᵒᵖ) :
    (inverseImageStructureIso f).hom.hom.app U =
      (Scheme.Site.ringUniverseLift.{u, u + 1}).map
        (RingCat.ofHom ((realizationIso f).hom.app U.unop).appTop.hom) := sorry
end AlgebraicGeometry.Scheme.Zariski.SmallToBig
