module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Limits.OverPost
public import stacks_project.Chap66.«66_27_0_4_Comparison»
public import stacks_project.Chap66.Lemma_66_27_1_LocalizationAt
public import stacks_project.Chap66.Lemma_66_27_2_Parameter

/-!
# Small-étale localization of a morphism of ringed topoi at a representable parameter

A morphism of algebraic spaces, together with étale scheme objects of the source and target,
determines the Modules-on-Sites localization of `f_small` on the identifications (66.27.0.4).
The inverse image is the 18.22.3 composite of localized inverse image with pullback along `s`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Slice topologies of `smallEtaleTopology` compose with `forget RingCat`. -/
instance smallEtaleTopology_over_hasSheafCompose_forget_ringCat
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleTopology X).over U).HasSheafCompose (forget RingCat.{u}) :=
  GrothendieckTopology.HasSheafCompose.over (smallEtaleTopology X) (forget RingCat.{u}) U

/-- Type-valued sheaves on a small étale site have pullbacks. -/
instance smallEtaleSheaf_hasPullbacks_type (X : AlgebraicSpace S) :
    HasPullbacks (Sheaf (smallEtaleTopology X) (Type u)) :=
  inferInstance

/-- Type-valued weak sheafification exists on slice topologies of `smallEtaleTopology`. -/
instance smallEtaleTopology_over_hasWeakSheafify_type
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    HasWeakSheafify ((smallEtaleTopology X).over U) (Type u) :=
  sorry

/-- Slice topologies of `smallEtaleTopology` are subcanonical. -/
instance smallEtaleTopology_over_subcanonical
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleTopology X).over U).Subcanonical :=
  sorry

/-- The opposite of `etaleLocalizationInverse` has left Kan extensions on type-valued
presheaves. -/
instance etaleLocalizationInverse_op_hasLeftKanExtension
    {Y : AlgebraicSpace S} {U : Over S} (e : ofOver U ⟶ Y) [Etale e]
    (P : (Over (smallEtaleSite.mk e))ᵒᵖ ⥤ Type u) :
    (etaleLocalizationInverse e).op.HasLeftKanExtension P :=
  sorry

/-- The opposite of `etaleLocalizationFunctor` has left Kan extensions on type-valued
presheaves. -/
instance etaleLocalizationFunctor_op_hasLeftKanExtension
    {Y : AlgebraicSpace S} {U : Over S} (e : ofOver U ⟶ Y) [Etale e]
    (P : (smallEtaleSite (ofOver U))ᵒᵖ ⥤ Type u) :
    (etaleLocalizationFunctor e).op.HasLeftKanExtension P :=
  sorry

/-- The opposite of `Over.forget` has left Kan extensions on type-valued presheaves. -/
instance smallEtaleOverForget_op_hasLeftKanExtension
    (X : AlgebraicSpace S) (U : smallEtaleSite X)
    (P : (Over U)ᵒᵖ ⥤ Type u) :
    (Over.forget U).op.HasLeftKanExtension P :=
  sorry

/-- Constructed pullback along `etaleLocalizationInverse` preserves finite limits. -/
instance etaleLocalizationInverse_sheafPullbackConstruction_preservesFiniteLimits
    {Y : AlgebraicSpace S} {U : Over S} (e : ofOver U ⟶ Y) [Etale e] :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (etaleLocalizationInverse e) (Type u)
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
        (smallEtaleTopology (ofOver U))) :=
  sorry

/-- Constructed pullback along `etaleLocalizationFunctor` preserves finite limits. -/
instance etaleLocalizationFunctor_sheafPullbackConstruction_preservesFiniteLimits
    {Y : AlgebraicSpace S} {U : Over S} (e : ofOver U ⟶ Y) [Etale e] :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (etaleLocalizationFunctor e) (Type u)
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e))) :=
  sorry

/-- Constructed pullback along `Over.forget` preserves finite limits. -/
instance smallEtaleOverForget_sheafPullbackConstruction_preservesFiniteLimits
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U) (Type u)
        ((smallEtaleTopology X).over U) (smallEtaleTopology X)) :=
  sorry

/-- The 18.22.3 inverse image of `f_small` preserves finite limits. -/
instance morphismOfTopoi_localization_pullback_preservesFiniteLimits
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y)
    {F : Sheaf (smallEtaleTopology X) (Type u)}
    (s : F ⟶ (morphismOfTopoi f).inverseImage.obj (etaleRepresentable V)) :
    PreservesFiniteLimits
      (((morphismOfTopoi f).localization (etaleRepresentable V)).inverseImage ⋙
        Over.pullback s) :=
  sorry

/-- The type-valued morphism of topoi presented by the forward étale localization
identification. -/
def etaleLocalizationIso_hom_morphismOfTopoi {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
      (smallEtaleTopology (ofOver U)) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      (Functor.sheafPullbackConstruction.sheafPullback (etaleLocalizationInverse e) (Type u)
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
        (smallEtaleTopology (ofOver U)))
  pushforward :=
    (etaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
      (smallEtaleTopology (ofOver U))
  adjunction :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleLocalizationInverse e)
      (Type u) ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
      (smallEtaleTopology (ofOver U))

/-- Coefficient-forgetful comparison for the forward étale localization identification. -/
def etaleLocalizationIso_hom_forgetIso {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    (etaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
          ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
          (smallEtaleTopology (ofOver U)) ⋙
        sheafCompose ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
          (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology (ofOver U)) (forget RingCat.{u}) ⋙
        (etaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
          ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
          (smallEtaleTopology (ofOver U)) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (etaleLocalizationInverse e)
      (forget RingCat.{u}) ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
      (smallEtaleTopology (ofOver U)))

/-- Direct-image ring compatibility of the forward étale localization identification. -/
theorem etaleLocalizationIso_hom_isRingCompatible {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    @Direct.IsRingCompatible
      (ringedSite (ofOver U)) ((ringedSite Y).localization (smallEtaleSite.mk e)) _ _
      (etaleLocalizationIso_hom_morphismOfTopoi e)
      ((etaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
        (smallEtaleTopology (ofOver U)))
      (etaleLocalizationIso_hom_forgetIso e)
      (etaleLocalizationIso e).hom.structureSheafMap :=
  sorry

/-- The forward identification `(U_étale, 𝒪_U) ⟶ localization of Y at U` as a morphism of
ringed topoi. -/
def etaleLocalizationIso_hom_toToposHom {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    RingedSite.ToposHom (ringedSite (ofOver U))
      ((ringedSite Y).localization (smallEtaleSite.mk e)) :=
  @ofDirectImage (ringedSite (ofOver U))
    ((ringedSite Y).localization (smallEtaleSite.mk e)) _ _
    (etaleLocalizationIso_hom_morphismOfTopoi e)
    ((etaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
      (smallEtaleTopology (ofOver U)))
    (etaleLocalizationIso_hom_forgetIso e)
    (etaleLocalizationIso e).hom.structureSheafMap
    (etaleLocalizationIso_hom_isRingCompatible e)

/-- The type-valued morphism of topoi presented by the inverse étale localization
identification. -/
def etaleLocalizationIso_inv_morphismOfTopoi {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e)) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      (Functor.sheafPullbackConstruction.sheafPullback (etaleLocalizationFunctor e) (Type u)
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e)))
  pushforward :=
    (etaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
  adjunction :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleLocalizationFunctor e)
      (Type u) (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e))

/-- Coefficient-forgetful comparison for the inverse étale localization identification. -/
def etaleLocalizationIso_inv_forgetIso {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    (etaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology (ofOver U))
          ((smallEtaleTopology Y).over (smallEtaleSite.mk e)) ⋙
        sheafCompose (smallEtaleTopology (ofOver U)) (forget RingCat.{u}) ≅
      sheafCompose ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
          (forget RingCat.{u}) ⋙
        (etaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology (ofOver U))
          ((smallEtaleTopology Y).over (smallEtaleSite.mk e)) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (etaleLocalizationFunctor e)
      (forget RingCat.{u}) (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e)))

/-- Direct-image ring compatibility of the inverse étale localization identification. -/
theorem etaleLocalizationIso_inv_isRingCompatible {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    @Direct.IsRingCompatible
      ((ringedSite Y).localization (smallEtaleSite.mk e)) (ringedSite (ofOver U)) _ _
      (etaleLocalizationIso_inv_morphismOfTopoi e)
      ((etaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e)))
      (etaleLocalizationIso_inv_forgetIso e)
      (etaleLocalizationIso e).inv.structureSheafMap :=
  sorry

/-- The inverse identification `localization of Y at U ⟶ (U_étale, 𝒪_U)` as a morphism of
ringed topoi. -/
def etaleLocalizationIso_inv_toToposHom {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    RingedSite.ToposHom ((ringedSite Y).localization (smallEtaleSite.mk e))
      (ringedSite (ofOver U)) :=
  @ofDirectImage ((ringedSite Y).localization (smallEtaleSite.mk e))
    (ringedSite (ofOver U)) _ _
    (etaleLocalizationIso_inv_morphismOfTopoi e)
    ((etaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk e)))
    (etaleLocalizationIso_inv_forgetIso e)
    (etaleLocalizationIso e).inv.structureSheafMap
    (etaleLocalizationIso_inv_isRingCompatible e)

/-- The base functor of `etaleLocalizationIso_hom_toToposHom` is `etaleLocalizationInverse`. -/
@[simp]
theorem etaleLocalizationIso_hom_toToposHom_pushforward {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    (etaleLocalizationIso_hom_toToposHom e).toTopos.pushforward =
      (etaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e))
        (smallEtaleTopology (ofOver U)) :=
  rfl

/-- The base functor of `etaleLocalizationIso_inv_toToposHom` is `etaleLocalizationFunctor`. -/
@[simp]
theorem etaleLocalizationIso_inv_toToposHom_pushforward {Y : AlgebraicSpace S} {U : Over S}
    (e : ofOver U ⟶ Y) [Etale e] :
    (etaleLocalizationIso_inv_toToposHom e).toTopos.pushforward =
      (etaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk e)) :=
  rfl


/-- Slice postcomposition along the small-étale inclusion of `X`. -/
def smallEtaleOverPost (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    Over U ⥤ Over ((smallEtaleInclusion X).obj U) :=
  @Over.post _ _ _ _ U (smallEtaleInclusion X)

/-- Postcomposition along `smallEtaleInclusion` is continuous on slice topologies. -/
instance instOverPost_smallEtaleInclusion_isContinuous (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (smallEtaleOverPost X U).IsContinuous
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) :=
  sorry

/-- Postcomposition along `smallEtaleInclusion` is cocontinuous on slice topologies. -/
instance instOverPost_smallEtaleInclusion_isCocontinuous (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (smallEtaleOverPost X U).IsCocontinuous
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) :=
  sorry

/-- Pointwise right Kan extensions exist for ring-valued sheaves along
`smallEtaleOverPost X U`. -/
instance instOverPost_smallEtaleInclusion_hasPointwiseRightKanExtension_ringCat
    (X : AlgebraicSpace S) (U : smallEtaleSite X)
    (P : (Over U)ᵒᵖ ⥤ RingCat.{u}) :
    (smallEtaleOverPost X U).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions exist for type-valued sheaves along
`smallEtaleOverPost X U`. -/
instance instOverPost_smallEtaleInclusion_hasPointwiseRightKanExtension_type
    (X : AlgebraicSpace S) (U : smallEtaleSite X)
    (P : (Over U)ᵒᵖ ⥤ Type u) :
    (smallEtaleOverPost X U).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The forgetful functor on rings preserves the right Kan extensions of
`smallEtaleOverPost X U`. -/
instance instOverPost_smallEtaleInclusion_forgetRingCat_preservesRightKanExtensions
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    (forget RingCat.{u}).PreservesRightKanExtensions
      (smallEtaleOverPost X U).op :=
  sorry

/-- Restriction from the spaces-étale slice to the scheme-étale slice is an
equivalence: scheme-étale objects form a dense subsite, also after localization.
This is a property of the specified restriction functor, not chosen comparison data. -/
instance smallEtaleLocalizationRestriction_isEquivalence
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).IsEquivalence :=
  sorry

/-- The explicit restriction/extension adjunction gives the comparison equivalence.
Its unit and counit, hence the inverse comparison, are fixed by that adjunction. -/
def smallEtaleLocalizationSheafEquivalence (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    Sheaf ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) (Type u) ≌
      Sheaf ((smallEtaleTopology X).over U) (Type u) :=
  ((smallEtaleOverPost X U).sheafAdjunctionCocontinuous (Type u)
    ((smallEtaleTopology X).over U)
    ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).toEquivalence

/-- Cocontinuous type-valued pushforward along `smallEtaleOverPost X U` is a
right adjoint. -/
instance instOverPost_smallEtaleInclusion_sheafPushforwardCocontinuous_type_isRightAdjoint
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleOverPost X U).sheafPushforwardCocontinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).IsRightAdjoint :=
  ((smallEtaleOverPost X U).sheafAdjunctionCocontinuous (Type u)
    ((smallEtaleTopology X).over U)
    ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).isRightAdjoint

/-- The left adjoint of type-valued cocontinuous pushforward along
`smallEtaleOverPost X U` preserves finite limits. -/
instance instOverPost_smallEtaleInclusion_leftAdjoint_preservesFiniteLimits
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    PreservesFiniteLimits
      ((smallEtaleOverPost X U).sheafPushforwardCocontinuous (Type u)
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).leftAdjoint :=
  by
    -- Local instance justification (search instability): pin the later instance to avoid search loops.
    letI : ((smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).IsRightAdjoint :=
      (smallEtaleLocalizationSheafEquivalence X U).symm.toAdjunction.isRightAdjoint
    exact preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq
      ((smallEtaleOverPost X U).sheafAdjunctionCocontinuous (Type u)
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
      (Adjunction.ofIsRightAdjoint _))

/-- Continuous type-valued pushforward along `smallEtaleOverPost X U` is a
right adjoint. -/
instance instOverPost_smallEtaleInclusion_sheafPushforwardContinuous_type_isRightAdjoint
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).IsRightAdjoint :=
  (smallEtaleLocalizationSheafEquivalence X U).symm.toAdjunction.isRightAdjoint

/-- The left adjoint of type-valued continuous pushforward along
`smallEtaleOverPost X U` preserves finite limits. -/
instance instOverPost_smallEtaleInclusion_continuous_leftAdjoint_preservesFiniteLimits
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    PreservesFiniteLimits
      ((smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).leftAdjoint :=
  preservesFiniteLimits_of_natIso (Adjunction.leftAdjointUniq
    (smallEtaleLocalizationSheafEquivalence X U).symm.toAdjunction
    (Adjunction.ofIsRightAdjoint _))

/-- The type-valued morphism of topoi from the small-étale slice at `U` to the spaces-étale
slice at the image of `U`. -/
def smallEtaleLocalizationComparisonMorphismOfTopoi (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u, u}
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))
      ((smallEtaleTopology X).over U) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
  pushforward :=
    (smallEtaleOverPost X U).sheafPushforwardCocontinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))
  adjunction :=
    (smallEtaleOverPost X U).sheafAdjunctionCocontinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))

/-- Coefficient-forgetful comparison for cocontinuous pushforward along
`smallEtaleOverPost X U`. -/
def smallEtaleLocalizationComparisonForgetIso (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (smallEtaleOverPost X U).sheafPushforwardCocontinuous RingCat.{u}
          ((smallEtaleTopology X).over U)
          ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) ⋙
        sheafCompose ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))
          (forget RingCat.{u}) ≅
      sheafCompose ((smallEtaleTopology X).over U) (forget RingCat.{u}) ⋙
        (smallEtaleOverPost X U).sheafPushforwardCocontinuous (Type u)
          ((smallEtaleTopology X).over U)
          ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (smallEtaleOverPost X U) (forget RingCat.{u})
    ((smallEtaleTopology X).over U)
    ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))

/-- Component at `W` of the restriction of the spaces-étale structure sheaf on the slice at
the image of `U` to the small-étale slice at `U`. -/
def smallEtaleLocalizationComparisonRestrictMapApp (X : AlgebraicSpace S)
    (U : smallEtaleSite X) (W : (Over U)ᵒᵖ) :
    (((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).obj
      ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U))).obj.obj W ⟶
    ((structureSheaf X).over U).obj.obj W :=
  (Functor.sheafPushforwardContinuousObjObjIso (smallEtaleOverPost X U) RingCat.{u}
      ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U)) (unop W)).hom ≫
    (Functor.sheafPushforwardContinuousObjObjIso
        (Over.forget ((smallEtaleInclusion X).obj U)) RingCat.{u}
        (spacesStructureSheaf X) ((smallEtaleOverPost X U).obj (unop W))).hom ≫
      (Functor.sheafPushforwardContinuousObjObjIso (smallEtaleInclusion X) RingCat.{u}
          (spacesStructureSheaf X) (unop W).left).inv ≫
        (((smallEtaleInclusion X).sheafAdjunctionCocontinuous RingCat.{u}
            (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app
          (structureSheaf X)).hom.app (op (unop W).left) ≫
          (Functor.sheafPushforwardContinuousObjObjIso (Over.forget U) RingCat.{u}
              (structureSheaf X) (unop W)).inv

/-- Restriction of the spaces-étale structure sheaf on the slice at the image of `U` to the
small-étale slice at `U`. -/
def smallEtaleLocalizationComparisonRestrictMap (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    ((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).obj
      ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U)) ⟶
    (structureSheaf X).over U :=
  ⟨{ app := fun W ↦ smallEtaleLocalizationComparisonRestrictMapApp X U W
     naturality := sorry }⟩

/-- Direct-image structure-sheaf map for the comparison from the small-étale localization at
`U` to the spaces-étale localization at the image of `U`. -/
def smallEtaleLocalizationComparisonStructureMap (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U) ⟶
      ((smallEtaleOverPost X U).sheafPushforwardCocontinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).obj
        ((structureSheaf X).over U) :=
  ((smallEtaleOverPost X U).sheafAdjunctionCocontinuous RingCat.{u}
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).homEquiv _ _
    (smallEtaleLocalizationComparisonRestrictMap X U)

/-- Direct-image ring compatibility of the small-to-spaces localization comparison. -/
theorem smallEtaleLocalizationComparison_isRingCompatible (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    @Direct.IsRingCompatible
      ((ringedSite X).localization U)
      ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U)) _ _
      (smallEtaleLocalizationComparisonMorphismOfTopoi X U)
      ((smallEtaleOverPost X U).sheafPushforwardCocontinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
      (smallEtaleLocalizationComparisonForgetIso X U)
      (smallEtaleLocalizationComparisonStructureMap X U) :=
  sorry

/-- Comparison morphism of ringed topoi from the small-étale localization at `U` to the
spaces-étale localization at the image of `U`. -/
def smallEtaleLocalizationComparison (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    RingedSite.ToposHom
      ((ringedSite X).localization U)
      ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U)) :=
  @ofDirectImage
    ((ringedSite X).localization U)
    ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U)) _ _
    (smallEtaleLocalizationComparisonMorphismOfTopoi X U)
    ((smallEtaleOverPost X U).sheafPushforwardCocontinuous RingCat.{u}
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
    (smallEtaleLocalizationComparisonForgetIso X U)
    (smallEtaleLocalizationComparisonStructureMap X U)
    (smallEtaleLocalizationComparison_isRingCompatible X U)

/-- The type-valued morphism of topoi from the spaces-étale slice at the image of `U` to the
small-étale slice at `U`. -/
def smallEtaleLocalizationComparisonInvMorphismOfTopoi (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u}
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) where
  inverseImageFunctor :=
    LeftExactFunctor.of (smallEtaleLocalizationSheafEquivalence X U).inverse
  pushforward :=
    (smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))
  adjunction :=
    (smallEtaleLocalizationSheafEquivalence X U).symm.toAdjunction

/-- Coefficient-forgetful comparison for continuous pushforward along
`smallEtaleOverPost X U`. -/
def smallEtaleLocalizationComparisonInvForgetIso (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
          ((smallEtaleTopology X).over U)
          ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) ⋙
        sheafCompose ((smallEtaleTopology X).over U) (forget RingCat.{u}) ≅
      sheafCompose ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))
          (forget RingCat.{u}) ⋙
        (smallEtaleOverPost X U).sheafPushforwardContinuous (Type u)
          ((smallEtaleTopology X).over U)
          ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose
      (smallEtaleOverPost X U) (forget RingCat.{u})
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))

/-- The counit of small-versus-spaces restriction ⊣ extension is invertible on `𝒪_X`. -/
instance smallEtaleInclusion_counit_structureSheaf_isIso (X : AlgebraicSpace S) :
    IsIso (((smallEtaleInclusion X).sheafAdjunctionCocontinuous RingCat.{u}
        (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app
      (structureSheaf X)) :=
  sorry

/-- Component at `W` of the direct-image structure-sheaf map from the small-étale slice at `U`
to the restricted spaces-étale structure sheaf. -/
def smallEtaleLocalizationComparisonInvStructureMapApp (X : AlgebraicSpace S)
    (U : smallEtaleSite X) (W : (Over U)ᵒᵖ) :
    ((structureSheaf X).over U).obj.obj W ⟶
      (((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
          ((smallEtaleTopology X).over U)
          ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).obj
        ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U))).obj.obj W :=
  (Functor.sheafPushforwardContinuousObjObjIso (Over.forget U) RingCat.{u}
      (structureSheaf X) (unop W)).hom ≫
    (inv (((smallEtaleInclusion X).sheafAdjunctionCocontinuous RingCat.{u}
            (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app
          (structureSheaf X))).hom.app (op (unop W).left) ≫
      (Functor.sheafPushforwardContinuousObjObjIso (smallEtaleInclusion X) RingCat.{u}
          (spacesStructureSheaf X) (unop W).left).hom ≫
        (Functor.sheafPushforwardContinuousObjObjIso
            (Over.forget ((smallEtaleInclusion X).obj U)) RingCat.{u}
            (spacesStructureSheaf X) ((smallEtaleOverPost X U).obj (unop W))).inv ≫
          (Functor.sheafPushforwardContinuousObjObjIso (smallEtaleOverPost X U) RingCat.{u}
              ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U)) (unop W)).inv

/-- Direct-image structure-sheaf map for the comparison from the spaces-étale localization at
the image of `U` to the small-étale localization at `U`. -/
def smallEtaleLocalizationComparisonInvStructureMap (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    (structureSheaf X).over U ⟶
      ((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U))).obj
        ((spacesStructureSheaf X).over ((smallEtaleInclusion X).obj U)) :=
  ⟨{ app := fun W ↦ smallEtaleLocalizationComparisonInvStructureMapApp X U W
     naturality := sorry }⟩

/-- Direct-image ring compatibility of the spaces-to-small localization comparison. -/
theorem smallEtaleLocalizationComparisonInv_isRingCompatible (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    @Direct.IsRingCompatible
      ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
      ((ringedSite X).localization U) _ _
      (smallEtaleLocalizationComparisonInvMorphismOfTopoi X U)
      ((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
      (smallEtaleLocalizationComparisonInvForgetIso X U)
      (smallEtaleLocalizationComparisonInvStructureMap X U) :=
  sorry

/-- Comparison morphism of ringed topoi from the spaces-étale localization at the image of `U`
to the small-étale localization at `U`. -/
def smallEtaleLocalizationComparisonInv (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
      ((ringedSite X).localization U) :=
  @ofDirectImage
    ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
    ((ringedSite X).localization U) _ _
    (smallEtaleLocalizationComparisonInvMorphismOfTopoi X U)
    ((smallEtaleOverPost X U).sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleTopology X).over U)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj U)))
    (smallEtaleLocalizationComparisonInvForgetIso X U)
    (smallEtaleLocalizationComparisonInvStructureMap X U)
    (smallEtaleLocalizationComparisonInv_isRingCompatible X U)

/-- The spaces-étale arrow of `X_spaces,étale` associated to a representable parameter
`s : h_U ⟶ f_small⁻¹ h_V`, obtained by transporting along
`smallEtaleInclusion Y ⋙ spacesEtalePullback f ≅ etaleBaseChange f`. -/
def ringedToposHom.localizationAt_spacesArrow {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : smallEtaleSite X} {V : smallEtaleSite Y}
    (c : (smallEtaleInclusion X).obj U ⟶ (etaleBaseChange f).obj V) :
    (smallEtaleInclusion X).obj U ⟶
      (spacesEtalePullback f).obj ((smallEtaleInclusion Y).obj V) :=
  c ≫ (smallEtaleInclusion_comp_spacesEtalePullback f).inv.app V

/-- The morphism of ringed topoi obtained by localizing `(f_small, f^♯)` at the representable
parameter corresponding to a spaces-étale arrow `c : U ⟶ V ×_Y X`. By Modules on Sites,
Lemma 18.22.4, this is the 18.22.3 localization at the associated sheaf map
`s : h_U ⟶ f_small⁻¹ h_V`. -/
def ringedToposHom.localizationAt {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : smallEtaleSite X} {V : smallEtaleSite Y}
    (c : (smallEtaleInclusion X).obj U ⟶ (etaleBaseChange f).obj V) :
    RingedSite.ToposHom ((ringedSite X).localization U) ((ringedSite Y).localization V) :=
  @RingedSite.ToposHom.comp
      ((ringedSite X).localization U)
      ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
      ((ringedSite Y).localization V) _ _ _
      (smallEtaleLocalizationComparison X U)
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
          ((spacesRingedSite Y).localization ((smallEtaleInclusion Y).obj V))
          ((ringedSite Y).localization V) _ _ _
          (spacesRingedHom.localizationAt f ((smallEtaleInclusion Y).obj V)
            (ringedToposHom.localizationAt_spacesArrow f c))
          (smallEtaleLocalizationComparisonInv Y V))

/-- `ringedToposHom.localizationAt` is the conjugate of `spacesRingedHom.localizationAt` along
the small-versus-spaces localization comparisons. -/
theorem ringedToposHom.localizationAt_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : smallEtaleSite X} {V : smallEtaleSite Y}
    (c : (smallEtaleInclusion X).obj U ⟶ (etaleBaseChange f).obj V) :
    ringedToposHom.localizationAt f c =
      @RingedSite.ToposHom.comp
          ((ringedSite X).localization U)
          ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
          ((ringedSite Y).localization V) _ _ _
          (smallEtaleLocalizationComparison X U)
          (@RingedSite.ToposHom.comp
              ((spacesRingedSite X).localization ((smallEtaleInclusion X).obj U))
              ((spacesRingedSite Y).localization ((smallEtaleInclusion Y).obj V))
              ((ringedSite Y).localization V) _ _ _
              (spacesRingedHom.localizationAt f ((smallEtaleInclusion Y).obj V)
                (ringedToposHom.localizationAt_spacesArrow f c))
              (smallEtaleLocalizationComparisonInv Y V)) :=
  rfl

section SliceParameter

variable {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The actual inverse-image functor of 18.22.3 at the sheaf map corresponding to `g`.
This lives on slices of sheaf categories; identifying it with the site-slice presentation
requires a separate representable-localization comparison. -/
def etaleRelocalizeSliceInverseImage (hcomm : p ≫ f = g ≫ q) :
    Over (etaleRepresentable (smallEtaleSite.mk q)) ⥤
      Over (etaleRepresentable (smallEtaleSite.mk p)) :=
  ((morphismOfTopoi f).localization (etaleRepresentable (smallEtaleSite.mk q))).inverseImage ⋙
    Over.pullback (etaleRelocalizeParameter p g f q hcomm)

/-- The ambient square for the same `s`, from the canonical product and pullback comparisons. -/
def etaleRelocalizeSliceAmbientIso (hcomm : p ≫ f = g ≫ q) :
    Over.star (etaleRepresentable (smallEtaleSite.mk q)) ⋙
        etaleRelocalizeSliceInverseImage p g f q hcomm ≅
      (morphismOfTopoi f).inverseImage ⋙ Over.star (etaleRepresentable (smallEtaleSite.mk p)) :=
  Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso (morphismOfTopoi f).inverseImage
        (etaleRepresentable (smallEtaleSite.mk q)))
      (Over.pullback (etaleRelocalizeParameter p g f q hcomm)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (morphismOfTopoi f).inverseImage
      (Over.starPullbackIsoStar (etaleRelocalizeParameter p g f q hcomm))

/-- The underlying structure-sheaf map for 18.22.3, using the same `s` as the inverse image.
The ambient comparison transports the structure map of `f`; no arbitrary map is selected. -/
def etaleRelocalizeSliceStructureMap (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeSliceInverseImage p g f q hcomm).obj
        ((Over.star (etaleRepresentable (smallEtaleSite.mk q))).obj
          (RingedSite.Hom.underlyingStructureSheaf (ringedSite Y))) ⟶
      (Over.star (etaleRepresentable (smallEtaleSite.mk p))).obj
        (RingedSite.Hom.underlyingStructureSheaf (ringedSite X)) :=
  (etaleRelocalizeSliceAmbientIso p g f q hcomm).hom.app
      (RingedSite.Hom.underlyingStructureSheaf (ringedSite Y)) ≫
    (Over.star (etaleRepresentable (smallEtaleSite.mk p))).map (ringedToposHom f).underlyingMap

/-- The displayed ambient square carries the actual structure map of `f` to the
constructed slice structure map. -/
theorem etaleRelocalizeSliceAmbientIso_structure (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeSliceAmbientIso p g f q hcomm).hom.app
        (RingedSite.Hom.underlyingStructureSheaf (ringedSite Y)) ≫
      (Over.star (etaleRepresentable (smallEtaleSite.mk p))).map (ringedToposHom f).underlyingMap =
        etaleRelocalizeSliceStructureMap p g f q hcomm :=
  rfl

end SliceParameter

end AlgebraicGeometry.AlgebraicSpace
