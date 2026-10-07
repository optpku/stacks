module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_27_1_Hom

/-!
# Composition of module pushforwards on algebraic spaces

Module direct image along a composite morphism of algebraic spaces is canonically isomorphic
to the composite of the two direct-image functors. The comparison is assembled from the
underlying type-valued topos pushforwards and the ringed-topos forgetful identifications.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Functor
open Sheaf.InternalModule
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Type-valued direct image along `α`, rewritten through spaces-étale pullback. -/
def typePushforwardFactor {X Y : AlgebraicSpace S} (α : X ⟶ Y) :
    typePushforward α ≅
      (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback α).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X))
    ((sheafPushforwardContinuousIso (smallEtaleInclusion_comp_spacesEtalePullback α)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      sheafPushforwardContinuousComp (smallEtaleInclusion Y) (spacesEtalePullback α)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The small étale inclusion is cover-dense in the spaces étale topology. -/
instance smallEtaleInclusion_isCoverDense (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y) :=
  sorry

/-- Spaces-étale pullback along a composite is continuous because each factor is. -/
instance spacesEtalePullback_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    (spacesEtalePullback β ⋙ spacesEtalePullback α).IsContinuous
      (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback β) (spacesEtalePullback α)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Restricting a spaces étale sheaf to the small étale site and extending it back is
isomorphic to the identity. -/
def smallEtaleInclusionContinuousCocontinuousIso (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) (Type u)) :=
  let restrict :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let extend :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  NatIso.ofComponents
    (fun F ↦
      let eSmall : restrict.obj ((restrict ⋙ extend).obj F) ≅ restrict.obj F :=
        { hom := adj.counit.app (restrict.obj F)
          inv := restrict.map (adj.unit.app F)
          hom_inv_id := sorry
          inv_hom_id := sorry }
      let i :
          (smallEtaleInclusion Y).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion Y).op ⋙ F.obj :=
        { hom := eSmall.hom.hom
          inv := eSmall.inv.hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      Functor.IsCoverDense.Types.sheafIso i)
    sorry

/-- Type-valued continuous pushforward along spaces-étale pullback respects composition. -/
def spacesEtaleTypePushforwardComp {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    (spacesEtalePullback α).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback β).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (α ≫ β)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback β).sheafPushforwardContinuousComp (spacesEtalePullback α) (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X) ≪≫
    sheafPushforwardContinuousIso (spacesEtalePullbackComp α β).symm (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Type-valued direct image along a composite is the composite of the type-valued direct
images. -/
def typePushforwardComp {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    typePushforward α ⋙ typePushforward β ≅ typePushforward (α ≫ β) :=
  let iX :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pF :=
    (spacesEtalePullback α).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback β).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleInclusion Z).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (typePushforwardFactor α) (typePushforward β) ≪≫
    Functor.associator iX (pF ⋙ iY) (typePushforward β) ≪≫
    isoWhiskerLeft iX (Functor.associator pF iY (typePushforward β)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (typePushforwardFactor β)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (Functor.associator iY
          ((smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (smallEtaleInclusionContinuousCocontinuousIso Y) (pG ⋙ iZ) ≪≫
        Functor.leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (Functor.associator pF pG iZ ≪≫
        isoWhiskerRight (spacesEtaleTypePushforwardComp α β) iZ) ≪≫
    (typePushforwardFactor (α ≫ β)).symm

/-- The underlying type-valued sheaf of an iterated module pushforward. -/
def pushforwardCompForgetIso {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    (pushforward α ⋙ pushforward β) ⋙
        ToInternal.underlying (structureSheaf Z) ≅
      ToInternal.underlying (structureSheaf X) ⋙
        typePushforward α ⋙ typePushforward β :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward α)
      (ModulePushforward.forgetIso (ringedToposHom β)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ModulePushforward.forgetIso (ringedToposHom α))
      (typePushforward β) ≪≫
    Functor.associator _ _ _

/-- The underlying type-valued comparison of iterated module pushforward with pushforward
along the composite. -/
def pushforwardCompHomUnderlying {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward α ⋙ pushforward β).obj M) ⟶
      (ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward (α ≫ β)).obj M) :=
  (pushforwardCompForgetIso α β).hom.app M ≫
    (typePushforwardComp α β).hom.app
      ((ToInternal.underlying (structureSheaf X)).obj M) ≫
    (ModulePushforward.forgetIso (ringedToposHom (α ≫ β))).inv.app M

/-- The reverse underlying type-valued comparison of composite pushforward. -/
def pushforwardCompInvUnderlying {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward (α ≫ β)).obj M) ⟶
      (ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward α ⋙ pushforward β).obj M) :=
  (ModulePushforward.forgetIso (ringedToposHom (α ≫ β))).hom.app M ≫
    (typePushforwardComp α β).inv.app
      ((ToInternal.underlying (structureSheaf X)).obj M) ≫
    (pushforwardCompForgetIso α β).inv.app M

/-- Pushforward of modules along a composite morphism of algebraic spaces is the composite
of the two pushforwards. -/
def pushforwardCompIso {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    pushforward α ⋙ pushforward β ≅ pushforward (α ≫ β) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf Z)
            (pushforwardCompHomUnderlying α β M) sorry sorry
        inv :=
          homOfUnderlying (structureSheaf Z)
            (pushforwardCompInvUnderlying α β M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Forgetting to type-valued sheaves, `pushforwardCompIso` is the composite of
`pushforwardCompForgetIso`, `typePushforwardComp`, and the forgetful iso of the composite. -/
theorem pushforwardCompIso_eq {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).map ((pushforwardCompIso α β).hom.app M) =
      pushforwardCompHomUnderlying α β M :=
  sorry

/-- The component of `pushforwardCompIso` at a module `M` has underlying type-valued
comparison `pushforwardCompHomUnderlying`. -/
theorem pushforwardCompIso_hom_app {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z)
    (M : X.Modules) :
    (ToInternal.underlying (structureSheaf Z)).map ((pushforwardCompIso α β).hom.app M) =
      (pushforwardCompForgetIso α β).hom.app M ≫
        (typePushforwardComp α β).hom.app
          ((ToInternal.underlying (structureSheaf X)).obj M) ≫
        (ModulePushforward.forgetIso (ringedToposHom (α ≫ β))).inv.app M :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
