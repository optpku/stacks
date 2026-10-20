/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom

/-!
# Identity and composition of module pullbacks on algebraic spaces

Module pullback along an identity (resp. a composite) of morphisms of algebraic spaces is
identified with the identity functor (resp. the composite of the pullbacks), as the left-adjoint
mate of an explicit comparison of module pushforwards on underlying type-valued sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Functor
open Opposite AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Spaces-étale pullback along a composite is continuous because each factor is. -/
instance spacesEtalePullback_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback g ⋙ spacesEtalePullback f).IsContinuous
      (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback g) (spacesEtalePullback f)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

namespace Modules

/-- Type-valued direct image along `f`, rewritten through spaces-étale pullback. -/
def typePushforwardFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    typePushforward f ≅
      AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension X ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleToSpaces Y).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension X)
    ((sheafPushforwardContinuousIso (smallEtaleInclusion_comp_spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      sheafPushforwardContinuousComp (smallEtaleToSpaces Y) (spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The small étale inclusion is cover-dense in the spaces étale topology. -/
instance smallEtaleInclusion_isCoverDense (Y : AlgebraicSpace S) :
    (smallEtaleToSpaces Y).IsCoverDense (spacesEtaleTopology Y) :=
  sorry

/-- The small étale inclusion is locally full in the spaces étale topology. -/
instance smallEtaleInclusion_isLocallyFull (Y : AlgebraicSpace S) :
    (smallEtaleToSpaces Y).IsLocallyFull (spacesEtaleTopology Y) :=
  sorry

/-- The small étale inclusion is locally faithful in the spaces étale topology. -/
instance smallEtaleInclusion_isLocallyFaithful (Y : AlgebraicSpace S) :
    (smallEtaleToSpaces Y).IsLocallyFaithful (spacesEtaleTopology Y) :=
  sorry

/-- The small étale site is a dense subsite of the spaces étale site. -/
instance smallEtaleInclusion_isDenseSubsite (Y : AlgebraicSpace S) :
    (smallEtaleToSpaces Y).IsDenseSubsite (smallEtaleTopology Y) (spacesEtaleTopology Y) where
  functorPushforward_mem_iff := sorry

/-- Restricting a spaces étale sheaf to the small étale site and extending it back is
isomorphic to the identity. -/
def smallEtaleInclusionContinuousCocontinuousIso (Y : AlgebraicSpace S) :
    (smallEtaleToSpaces Y).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension Y ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) (Type u)) :=
  (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.restrictionExtensionIso Y).symm

/-- Type-valued continuous pushforward along spaces-étale pullback respects composition. -/
def spacesEtaleTypePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f) (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X) ≪≫
    sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Type-valued direct image along a composite is the composite of the type-valued direct
images. -/
def typePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typePushforward f ⋙ typePushforward g ≅ typePushforward (f ≫ g) :=
  let iX :=
    AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension X
  let pF :=
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleToSpaces Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleToSpaces Z).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (typePushforwardFactor f) (typePushforward g) ≪≫
    Functor.associator iX (pF ⋙ iY) (typePushforward g) ≪≫
    isoWhiskerLeft iX (Functor.associator pF iY (typePushforward g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (typePushforwardFactor g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (Functor.associator iY
          (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension Y)
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (smallEtaleInclusionContinuousCocontinuousIso Y) (pG ⋙ iZ) ≪≫
        Functor.leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (Functor.associator pF pG iZ ≪≫
        isoWhiskerRight (spacesEtaleTypePushforwardComp f g) iZ) ≪≫
    (typePushforwardFactor (f ≫ g)).symm

/-- The underlying type-valued sheaf of an iterated module pushforward. -/
def pushforwardCompForgetIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward f ⋙ pushforward g) ⋙
        Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z) ≅
      Sheaf.InternalModule.ToInternal.underlying (structureSheaf X) ⋙
        typePushforward f ⋙ typePushforward g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward f)
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f))
      (typePushforward g) ≪≫
    Functor.associator _ _ _

/-- The underlying type-valued comparison of iterated module pushforward with pushforward
along the composite. -/
def pushforwardCompHomUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward f ⋙ pushforward g).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward (f ≫ g)).obj M) :=
  (pushforwardCompForgetIso f g).hom.app M ≫
    (typePushforwardComp f g).hom.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).inv.app M

/-- The reverse underlying type-valued comparison of composite pushforward. -/
def pushforwardCompInvUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward (f ≫ g)).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward f ⋙ pushforward g).obj M) :=
  (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).hom.app M ≫
    (typePushforwardComp f g).inv.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (pushforwardCompForgetIso f g).inv.app M

/-- The composition of module pushforwards along `f` then `g` identifies with pushforward
along `f ≫ g`. -/
def pushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompHomUnderlying f g M) sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompInvUnderlying f g M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Successive module pullbacks identify with pullback along the composite morphism, as the
left-adjoint mate of `pushforwardComp`. -/
def pullbackCompIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g)

/-- Spaces-étale pullback along an identity morphism is isomorphic to the identity functor. -/
def spacesEtalePullbackId (X : AlgebraicSpace S) :
    spacesEtalePullback (𝟙 X) ≅ 𝟭 (spacesEtaleSite X) :=
  NatIso.ofComponents
    (fun V ↦
      MorphismProperty.Over.isoMk
        { hom := pullback.fst V.hom (𝟙 X)
          inv := pullback.lift (𝟙 V.left) V.hom (Category.comp_id V.hom).symm
          hom_inv_id := sorry
          inv_hom_id := sorry }
        sorry)
    sorry

/-- Type-valued direct image along an identity morphism is isomorphic to the identity. -/
def typePushforwardId (X : AlgebraicSpace S) :
    typePushforward (𝟙 X) ≅ 𝟭 (Sheaf (smallEtaleTopology X) (Type u)) :=
  typePushforwardFactor (𝟙 X) ≪≫
    isoWhiskerLeft
      (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension X)
      (isoWhiskerRight
        (sheafPushforwardContinuousId' (spacesEtalePullbackId X) (Type u)
          (spacesEtaleTopology X))
        ((smallEtaleToSpaces X).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology X) (spacesEtaleTopology X))) ≪≫
    isoWhiskerLeft
      (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extension X)
      (Functor.leftUnitor
        ((smallEtaleToSpaces X).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology X) (spacesEtaleTopology X))) ≪≫
    AlgebraicGeometry.AlgebraicSpace.EtaleTopos.extensionRestrictionIso X

/-- The underlying type-valued sheaf of module pushforward along an identity. -/
def pushforwardIdForgetIso (X : AlgebraicSpace S) :
    pushforward (𝟙 X) ⋙
        Sheaf.InternalModule.ToInternal.underlying (structureSheaf X) ≅
      Sheaf.InternalModule.ToInternal.underlying (structureSheaf X) ⋙
        typePushforward (𝟙 X) :=
  RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (𝟙 X))

/-- The underlying type-valued comparison of identity module pushforward with the identity. -/
def pushforwardIdHomUnderlying (X : AlgebraicSpace S) (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      ((pushforward (𝟙 X)).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M :=
  (pushforwardIdForgetIso X).hom.app M ≫
    (typePushforwardId X).hom.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M)

/-- The reverse underlying type-valued comparison of identity module pushforward. -/
def pushforwardIdInvUnderlying (X : AlgebraicSpace S) (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        ((pushforward (𝟙 X)).obj M) :=
  (typePushforwardId X).inv.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (pushforwardIdForgetIso X).inv.app M

/-- Module pushforward along an identity morphism is isomorphic to the identity functor. -/
def pushforwardId (X : AlgebraicSpace S) :
    pushforward (𝟙 X) ≅ 𝟭 X.Modules :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
            (pushforwardIdHomUnderlying X M) sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
            (pushforwardIdInvUnderlying X M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Module pullback along an identity morphism is isomorphic to the identity functor, as the
left-adjoint mate of `pushforwardId`. -/
def pullbackIdIso (X : AlgebraicSpace S) :
    pullback (𝟙 X) ≅ 𝟭 X.Modules :=
  Adjunction.leftAdjointIdIso (pullbackPushforwardAdjunction (𝟙 X)) (pushforwardId X)

end Modules

end AlgebraicGeometry.AlgebraicSpace
