/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.«66_27_0_2_RingedSite»
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Spaces-étale morphisms of ringed sites

A morphism of algebraic spaces induces a morphism of spaces-étale ringed sites
`(f_spaces,étale, f^♯)` with base functor `spacesEtalePullback f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The small étale inclusion is locally full on the spaces-étale topology. -/
instance smallEtaleInclusion_isLocallyFull (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsLocallyFull (spacesEtaleTopology X) :=
  sorry

/-- The comparison map from the categorical fibre product `V ×_Y X` to the
functor-of-points fibre product used by `etaleBaseChange`. -/
def spacesEtalePullbackInclusionSpaceIsoHom (f : X ⟶ Y) (U : smallEtaleSite Y) :
    pullback U.hom f ⟶ etaleBaseChangeSpace f U :=
  let fstFun : (pullback U.hom f).functorOfPoints ⟶
      (ofOver U.left).functorOfPoints :=
    pullback.fst U.hom f
  let sndFun : (pullback U.hom f).functorOfPoints ⟶ X.functorOfPoints :=
    pullback.snd U.hom f
  pullback.lift sndFun fstFun sorry

/-- The fibre product `V ×_Y X` computed in `AlgebraicSpace S` is isomorphic to the
functor-of-points fibre product used by `etaleBaseChange`. -/
def spacesEtalePullbackInclusionSpaceIso (f : X ⟶ Y) (U : smallEtaleSite Y) :
    pullback U.hom f ≅ etaleBaseChangeSpace f U where
  hom := spacesEtalePullbackInclusionSpaceIsoHom f U
  inv := pullback.lift (etaleBaseChangeSnd f U) (etaleBaseChangeHom f U) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The composite `smallEtaleInclusion Y ⋙ spacesEtalePullback f` is continuous. -/
instance smallEtaleInclusion_comp_spacesEtalePullback_isContinuous (f : X ⟶ Y) :
    (smallEtaleInclusion Y ⋙ spacesEtalePullback f).IsContinuous
      (smallEtaleTopology Y) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (smallEtaleInclusion Y) (spacesEtalePullback f)
    (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Pullback of a scheme étale over `Y` along `f` agrees, as an object of `X_spaces,étale`,
with `etaleBaseChange`. -/
def smallEtaleInclusion_comp_spacesEtalePullback (f : X ⟶ Y) :
    smallEtaleInclusion Y ⋙ spacesEtalePullback f ≅ etaleBaseChange f :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk (spacesEtalePullbackInclusionSpaceIso f U) sorry)
    sorry

/-- On objects, `smallEtaleInclusion_comp_spacesEtalePullback` is
`spacesEtalePullbackInclusionSpaceIso`. -/
theorem smallEtaleInclusion_comp_spacesEtalePullback_app_left (f : X ⟶ Y)
    (U : smallEtaleSite Y) :
    ((smallEtaleInclusion_comp_spacesEtalePullback f).hom.app U).left =
      (spacesEtalePullbackInclusionSpaceIso f U).hom :=
  rfl

/-- Continuous sheaf pushforward along `spacesEtalePullback f` is a right adjoint on
type-valued sheaves. -/
instance spacesEtalePullback_sheafPushforwardContinuous_type_isRightAdjoint (f : X ⟶ Y) :
    ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)).IsRightAdjoint :=
  sorry

/-- The left adjoint of type-valued continuous pushforward along `spacesEtalePullback f`
preserves finite limits. -/
instance spacesEtalePullback_leftAdjoint_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).leftAdjoint :=
  sorry

/-- The small-étale structure map of `f`, transported along
`smallEtaleInclusion Y ⋙ spacesEtalePullback f ≅ etaleBaseChange f` to a map
`𝒪_Y^{small} ⟶ i_Y^* (f_spaces,étale)_* 𝒪_X`. -/
def spacesStructureSheafMapSmall (f : X ⟶ Y) :
    structureSheaf Y ⟶
      ((smallEtaleInclusion Y).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).obj
        (((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
            (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
          (spacesStructureSheaf X)) :=
  EtaleRingedTopos.ringExtensionStructureMap f ≫
    (Functor.sheafPushforwardContinuousComp'
        (smallEtaleInclusion_comp_spacesEtalePullback f) RingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)).inv.app
      (spacesStructureSheaf X)

/-- The direct-image structure-sheaf map `𝒪_Y ⟶ (f_spaces,étale)_* 𝒪_X` on spaces-étale
sites, obtained as the cover-dense extension of the small-étale map `f^♯` along
`smallEtaleInclusion`. -/
def spacesStructureSheafMap (f : X ⟶ Y) :
    spacesStructureSheaf Y ⟶
      ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
        (spacesStructureSheaf X) :=
  InducedCategory.homMk
    (Functor.IsCoverDense.sheafHom
      (((EtaleRingedTopos.ringExtensionRestrictionIso Y).hom.app (structureSheaf Y)).hom ≫
        (spacesStructureSheafMapSmall f).hom))

/-- Restriction of `spacesStructureSheafMap` along `smallEtaleInclusion Y` recovers
`spacesStructureSheafMapSmall`. -/
theorem spacesStructureSheafMapSmall_spec (f : X ⟶ Y) :
    (EtaleRingedTopos.ringExtensionRestrictionIso Y).hom.app (structureSheaf Y) ≫
      spacesStructureSheafMapSmall f =
    ((smallEtaleInclusion Y).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology Y)).map
        (spacesStructureSheafMap f) :=
  sorry

/-- The morphism of spaces-étale ringed sites associated to a morphism of algebraic spaces. -/
def spacesRingedHom (f : X ⟶ Y) :
    RingedSite.Hom (spacesRingedSite X) (spacesRingedSite Y) where
  base := spacesEtalePullback f
  structureSheafMap := spacesStructureSheafMap f

/-- The base functor of `spacesRingedHom f` is `spacesEtalePullback f`. -/
@[simp]
theorem spacesRingedHom_base (f : X ⟶ Y) :
    (spacesRingedHom f).base = spacesEtalePullback f :=
  rfl

/-- The structure-sheaf map of `spacesRingedHom f` is `spacesStructureSheafMap f`. -/
@[simp]
theorem spacesRingedHom_structureSheafMap (f : X ⟶ Y) :
    (spacesRingedHom f).structureSheafMap = spacesStructureSheafMap f :=
  rfl

/-- Coefficient-forgetful comparison for continuous pushforward along `spacesEtalePullback`. -/
def spacesRingedHom_forgetIso (f : X ⟶ Y) :
    (spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (spacesEtaleTopology X) (forget RingCat.{u}) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (spacesEtalePullback f)
      (forget RingCat.{u}) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The type-valued morphism of topoi presented by `spacesEtalePullback f` on sheaves of
types in universe `u`. -/
def spacesRingedMorphismOfTopoi (f : X ⟶ Y) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleTopology Y) (spacesEtaleTopology X) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).leftAdjoint
  pushforward :=
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  adjunction :=
    Adjunction.ofIsRightAdjoint
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The direct image of `spacesRingedMorphismOfTopoi f` is continuous sheaf pushforward
along `spacesEtalePullback f`. -/
theorem spacesRingedMorphismOfTopoi_pushforward (f : X ⟶ Y) :
    (spacesRingedMorphismOfTopoi f).pushforward =
      (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Direct-image ring compatibility of `spacesRingedHom f`. -/
theorem spacesRingedHom_isRingCompatible (f : X ⟶ Y) :
    @Direct.IsRingCompatible (spacesRingedSite X) (spacesRingedSite Y) _ _
      (spacesRingedMorphismOfTopoi f)
      ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology Y) (spacesEtaleTopology X))
      (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f) :=
  sorry

/-- The morphism of spaces-étale ringed topoi associated to a morphism of algebraic spaces,
packaged by `ofDirectImage` so that `UnivLE.{u+1,u}` is not required. -/
def spacesRingedToposHom (f : X ⟶ Y) :
    RingedSite.ToposHom (spacesRingedSite X) (spacesRingedSite Y) :=
  @ofDirectImage (spacesRingedSite X) (spacesRingedSite Y) _ _
    (spacesRingedMorphismOfTopoi f)
    ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology Y) (spacesEtaleTopology X))
    (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f)
    (spacesRingedHom_isRingCompatible f)

/-- `spacesRingedToposHom f` is the `ofDirectImage` packaging of `spacesRingedHom f`. -/
theorem spacesRingedToposHom_eq (f : X ⟶ Y) :
    spacesRingedToposHom f =
      @ofDirectImage (spacesRingedSite X) (spacesRingedSite Y) _ _
        (spacesRingedMorphismOfTopoi f)
        ((spacesEtalePullback f).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology Y) (spacesEtaleTopology X))
        (spacesRingedHom_forgetIso f) (spacesStructureSheafMap f)
        (spacesRingedHom_isRingCompatible f) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
