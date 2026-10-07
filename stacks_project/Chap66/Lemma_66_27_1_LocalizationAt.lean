module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import stacks_project.Chap66.Lemma_66_16_6_Postcomp
public import stacks_project.Chap66.Lemma_66_27_1_BaseChange
public import stacks_project.Chap66.Lemma_66_27_1_Hom

/-!
# Spaces-étale localization of a morphism of ringed topoi

A morphism of algebraic spaces, together with an object of the target spaces-étale site and an
arrow into its pullback, determines the Modules-on-Sites localization `f_c` without imposing
`UnivLE.{u+1,u}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Slice topologies of `spacesEtaleTopology` compose with `forget RingCat`. -/
instance spacesEtaleTopology_over_hasSheafCompose_forget_ringCat
    (X : AlgebraicSpace S) (U : spacesEtaleSite X) :
    ((spacesEtaleTopology X).over U).HasSheafCompose (forget RingCat.{u}) :=
  GrothendieckTopology.HasSheafCompose.over (spacesEtaleTopology X) (forget RingCat.{u}) U

/-- The étale site of algebraic spaces over `X` has fibre products. -/
instance spacesEtaleSite_hasPullbacks (X : AlgebraicSpace S) :
    HasPullbacks (spacesEtaleSite X) :=
  inferInstance

/-- Pointwise right Kan extensions exist for relocalization of ring-valued sheaves on spaces-étale
slices. -/
instance instOverMap_hasPointwiseRightKanExtension_ringCat
    {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (h : A ⟶ B)
    (P : (Over A)ᵒᵖ ⥤ RingCat.{u}) :
    (Over.map h).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions exist for relocalization of type-valued sheaves on spaces-étale
slices. -/
instance instOverMap_hasPointwiseRightKanExtension_type
    {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (h : A ⟶ B)
    (P : (Over A)ᵒᵖ ⥤ Type u) :
    (Over.map h).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Postcomposition on spaces-étale slices is cocontinuous. -/
instance instOverMap_isCocontinuous {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z}
    (h : A ⟶ B) :
    (Over.map h).IsCocontinuous
      ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B) :=
  sorry

/-- Slice pullback along an arrow of `X_spaces,étale` is continuous. -/
instance instOverPullback_isContinuous {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z}
    (h : A ⟶ B) :
    (Over.Site.pullbackFunctor h).IsContinuous
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  sorry

/-- The forgetful functor on rings preserves the right Kan extensions used by relocalization. -/
instance instOverMap_forgetRingCat_preservesRightKanExtensions
    {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (h : A ⟶ B) :
    (forget RingCat.{u}).PreservesRightKanExtensions (Over.map h).op :=
  sorry

/-- Cocontinuous type-valued pushforward along `Over.map` on spaces-étale slices is a right
adjoint. -/
instance instOverMap_sheafPushforwardCocontinuous_type_isRightAdjoint
    {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (h : A ⟶ B) :
    ((Over.map h).sheafPushforwardCocontinuous (Type u)
      ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B)).IsRightAdjoint :=
  sorry

/-- The left adjoint of type-valued cocontinuous pushforward along `Over.map` preserves finite
limits. -/
instance spacesRingedHom.overMap_leftAdjoint_preservesFiniteLimits
    {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (h : A ⟶ B) :
    PreservesFiniteLimits
      ((Over.map h).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B)).leftAdjoint :=
  sorry

/-- Continuous type-valued pushforward along `Over.post (spacesEtalePullback f)` is a right
adjoint. -/
instance spacesRingedHom.overPost_isRightAdjoint
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) (T : spacesEtaleSite W) :
    ((Over.post (spacesEtalePullback e)).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology W).over T)
      ((spacesEtaleTopology Z).over ((spacesEtalePullback e).obj T))).IsRightAdjoint :=
  sorry

/-- The left adjoint of type-valued continuous pushforward along
`Over.post (spacesEtalePullback f)` preserves finite limits. -/
instance instOverPost_spacesEtalePullback_leftAdjoint_preservesFiniteLimits
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) (T : spacesEtaleSite W) :
    PreservesFiniteLimits
      ((Over.post (spacesEtalePullback e)).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology W).over T)
        ((spacesEtaleTopology Z).over ((spacesEtalePullback e).obj T))).leftAdjoint :=
  sorry

/-- The type-valued morphism of topoi presented by relocalization along an arrow of
`X_spaces,étale`. -/
def spacesRingedHom.relocalizationMorphismOfTopoi {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      ((spacesEtaleTopology X).over V) ((spacesEtaleTopology X).over U) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((Over.map c).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)).leftAdjoint
  pushforward :=
    (Over.map c).sheafPushforwardCocontinuous (Type u)
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)
  adjunction :=
    Adjunction.ofIsRightAdjoint
      ((Over.map c).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V))

/-- Coefficient-forgetful comparison for cocontinuous pushforward along `Over.map`. -/
def spacesRingedHom.relocalizationForgetIso {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (Over.map c).sheafPushforwardCocontinuous RingCat.{u}
          ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) ⋙
        sheafCompose ((spacesEtaleTopology X).over V) (forget RingCat.{u}) ≅
      sheafCompose ((spacesEtaleTopology X).over U) (forget RingCat.{u}) ⋙
        (Over.map c).sheafPushforwardCocontinuous (Type u)
          ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso (Over.map c) (forget RingCat.{u})
    ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)

/-- The direct-image structure-sheaf map for relocalization along an arrow of
`X_spaces,étale`. -/
def spacesRingedHom.relocalizationStructureMap {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (spacesStructureSheaf X).over V ⟶
      ((Over.map c).sheafPushforwardCocontinuous RingCat.{u}
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)).obj
        ((spacesStructureSheaf X).over U) :=
  ((Over.map c).sheafAdjunctionCocontinuous RingCat.{u}
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)).homEquiv _ _
    ((Functor.sheafPushforwardContinuousComp' (Over.mapForget c) RingCat.{u}
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V)
        (spacesEtaleTopology X)).app (spacesStructureSheaf X)).hom

/-- Direct-image ring compatibility of spaces-étale relocalization. -/
theorem spacesRingedHom.relocalization_isRingCompatible {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    @Direct.IsRingCompatible
      ((spacesRingedSite X).localization U) ((spacesRingedSite X).localization V) _ _
      (spacesRingedHom.relocalizationMorphismOfTopoi c)
      ((Over.map c).sheafPushforwardCocontinuous RingCat.{u}
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V))
      (spacesRingedHom.relocalizationForgetIso c)
      (spacesRingedHom.relocalizationStructureMap c) :=
  sorry

/-- Relocalization along an arrow of `X_spaces,étale`, as a morphism of localized ringed topoi. -/
def spacesRingedHom.relocalization {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization U) ((spacesRingedSite X).localization V) :=
  @ofDirectImage
    ((spacesRingedSite X).localization U) ((spacesRingedSite X).localization V) _ _
    (spacesRingedHom.relocalizationMorphismOfTopoi c)
    ((Over.map c).sheafPushforwardCocontinuous RingCat.{u}
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V))
    (spacesRingedHom.relocalizationForgetIso c)
    (spacesRingedHom.relocalizationStructureMap c)
    (spacesRingedHom.relocalization_isRingCompatible c)

/-- The type-valued morphism of topoi presented by `Over.post (spacesEtalePullback f)`. -/
def spacesRingedHom.localizationMorphismOfTopoi {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      ((spacesEtaleTopology Y).over V)
      ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology Y).over V)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V))).leftAdjoint
  pushforward :=
    (Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology Y).over V)
      ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V))
  adjunction :=
    Adjunction.ofIsRightAdjoint
      ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology Y).over V)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)))

/-- Coefficient-forgetful comparison for continuous pushforward along
`Over.post (spacesEtalePullback f)`. -/
def spacesRingedHom.localizationForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    (Over.post (spacesEtalePullback f)).sheafPushforwardContinuous RingCat.{u}
          ((spacesEtaleTopology Y).over V)
          ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)) ⋙
        sheafCompose ((spacesEtaleTopology Y).over V) (forget RingCat.{u}) ≅
      sheafCompose ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V))
          (forget RingCat.{u}) ⋙
        (Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
          ((spacesEtaleTopology Y).over V)
          ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (Over.post (spacesEtalePullback f))
      (forget RingCat.{u}) ((spacesEtaleTopology Y).over V)
      ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)))

/-- Direct-image ring compatibility of the Modules-on-Sites localization of
`spacesRingedHom f` at `V`. -/
theorem spacesRingedHom.localization_isRingCompatible {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    @Direct.IsRingCompatible
      ((spacesRingedSite X).localization ((spacesEtalePullback f).obj V))
      ((spacesRingedSite Y).localization V) _ _
      (spacesRingedHom.localizationMorphismOfTopoi f V)
      ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over V)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)))
      (spacesRingedHom.localizationForgetIso f V)
      (RingedSite.Hom.localization (spacesRingedHom f) V).structureSheafMap :=
  sorry

/-- The morphism of ringed topoi obtained by localizing `spacesRingedHom f` at an object of
`Y_spaces,étale`. -/
def spacesRingedHom.localizationToposHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization ((spacesEtalePullback f).obj V))
      ((spacesRingedSite Y).localization V) :=
  @ofDirectImage
    ((spacesRingedSite X).localization ((spacesEtalePullback f).obj V))
    ((spacesRingedSite Y).localization V) _ _
    (spacesRingedHom.localizationMorphismOfTopoi f V)
    ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous RingCat.{u}
      ((spacesEtaleTopology Y).over V)
      ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)))
    (spacesRingedHom.localizationForgetIso f V)
    (RingedSite.Hom.localization (spacesRingedHom f) V).structureSheafMap
    (spacesRingedHom.localization_isRingCompatible f V)

/-- The base functor of `spacesRingedHom.localizationToposHom f V` is postcomposition with
`spacesEtalePullback f`. -/
theorem spacesRingedHom.localizationToposHom_pushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) :
    (spacesRingedHom.localizationToposHom f V).toTopos.pushforward =
      (Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology Y).over V)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V)) :=
  rfl

/-- Modules-on-Sites localization of `(f_spaces,étale, f^♯)` at an arrow
`c : U ⟶ V ×_Y X` of `X_spaces,étale`. -/
def spacesRingedHom.localizationAt {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) {U : spacesEtaleSite X}
    (c : U ⟶ (spacesEtalePullback f).obj V) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization U) ((spacesRingedSite Y).localization V) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization U)
      ((spacesRingedSite X).localization ((spacesEtalePullback f).obj V))
      ((spacesRingedSite Y).localization V) _ _ _
      (spacesRingedHom.relocalization c)
      (spacesRingedHom.localizationToposHom f V)

/-- `spacesRingedHom.localizationAt` is relocalization along `c` followed by localization of
`spacesRingedHom f` at `V`. -/
theorem spacesRingedHom.localizationAt_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : spacesEtaleSite Y) {U : spacesEtaleSite X}
    (c : U ⟶ (spacesEtalePullback f).obj V) :
    spacesRingedHom.localizationAt f V c =
      @RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization U)
          ((spacesRingedSite X).localization ((spacesEtalePullback f).obj V))
          ((spacesRingedSite Y).localization V) _ _ _
          (spacesRingedHom.relocalization c)
          (spacesRingedHom.localizationToposHom f V) :=
  rfl

/-- The continuous pullback presentation of relocalization along an arrow of
`X_spaces,étale`. -/
def spacesRingedHom.relocalizationPullbackPresentation {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (Over.map c).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) ≅
      (Over.Site.pullbackFunctor c).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology X).over V) ((spacesEtaleTopology X).over U) :=
  Over.Site.DirectImage.pullbackPresentation (spacesEtaleTopology X) c

end AlgebraicGeometry.AlgebraicSpace
