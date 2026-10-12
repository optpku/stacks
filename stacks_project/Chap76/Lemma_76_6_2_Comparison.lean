/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import stacks_project.Chap76.Lemma_76_5_2_Comparison
public import stacks_project.Chap76.Lemma_76_25_1_Pullback
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import stacks_project.Chap76.«76_6_1_2_Comparison»

/-!
# Étale-chart comparison of total conormal algebras of immersions

For an immersion `i : Z ⟶ X` of algebraic spaces over a scheme `S` and an étale
morphism `φ : U ⟶ X` from a scheme, restriction of `C_{Z/X,*}` to
`Z_U = U ×_X Z` is canonically identified with `C_{Z_U/U,*}` as quasi-coherent
`𝒪_{Z_U}`-algebras, functorially in the étale chart `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}}

/-- Type-valued sheaves on a small étale site carry the canonical cartesian braiding. -/
instance instBraidedCategory_smallEtaleType (Y : AlgebraicSpace S) :
    BraidedCategory (Sheaf (smallEtaleTopology Y) (Type u)) :=
  CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory.{u + 1, u, u}
    (smallEtaleTopology Y)

/-- Equal morphisms of algebraic spaces induce isomorphic algebra pullbacks. -/
def pullbackCongr {Y W : AlgebraicSpace S} {f g : Y ⟶ W} (h : f = g) :
    QcAlgebraUnder.pullback f ≅ QcAlgebraUnder.pullback g :=
  eqToIso (congrArg QcAlgebraUnder.pullback h)

/-- Inverse image of types along a composite morphism of algebraic spaces. -/
def typeInverseImageComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    (morphismOfTopoi g).inverseImage ⋙ (morphismOfTopoi f).inverseImage ≅
      (morphismOfTopoi (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (morphismOfTopoi g).adjunction (morphismOfTopoi f).adjunction
    (morphismOfTopoi (f ≫ g)).adjunction (Modules.typePushforwardComp f g)

/-- The inverse image of a morphism of small étale topoi preserves finite products. -/
instance instPreservesFiniteLimits_morphismOfTopoi_inverseImage
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    PreservesFiniteLimits (morphismOfTopoi f).inverseImage :=
  LeftExactAdjunction.inverseImagePreservesFiniteLimits (morphismOfTopoi f)

/-- Direct image of types along a morphism of algebraic spaces preserves finite products. -/
instance instPreservesFiniteProducts_morphismOfTopoi_pushforward
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    PreservesFiniteProducts (morphismOfTopoi f).pushforward :=
  LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f)

/-- Small étale sheaves of commutative rings compose with the forgetful functor to types. -/
instance smallEtaleTopology_hasSheafCompose_forget_commRing (Y : AlgebraicSpace S) :
    (smallEtaleTopology Y).HasSheafCompose (CategoryTheory.forget CommRingCat.{u}) :=
  sorry

/-- Direct image of commutative-ring sheaves corresponding to `pullbackSheafFunctor`. -/
def pullbackSheafPushforward {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology W) CommRingCat.{u} :=
  toInternal.{u + 1, u, u} ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology W) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology W))
      (morphismOfTopoi f).pushforward inferInstance) ⋙
    fromInternal.{u + 1, u, u}

/-- Inverse image of commutative-ring sheaves is left adjoint to the internal direct image. -/
def pullbackSheafFunctorAdjunction {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    QcAlgebraUnder.pullbackSheafFunctor f ⊣ pullbackSheafPushforward f :=
  ((CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
        (J := smallEtaleTopology W)).toAdjunction.comp
      (@Functor.mapCommRingOfFiniteProductsAdjunction
        (Sheaf (smallEtaleTopology W) (Type u)) _ _
        (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory.{u + 1, u, u}
          (smallEtaleTopology W))
        (Sheaf (smallEtaleTopology Y) (Type u)) _ _
        (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory.{u + 1, u, u}
          (smallEtaleTopology Y))
        (morphismOfTopoi f).inverseImage inferInstance
        (morphismOfTopoi f).pushforward inferInstance
        (morphismOfTopoi f).adjunction)).comp
    (CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
        (J := smallEtaleTopology Y)).symm.toAdjunction

/-- Inverse image of commutative-ring sheaves is a left adjoint. -/
instance instIsLeftAdjoint_pullbackSheafFunctor {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    (QcAlgebraUnder.pullbackSheafFunctor f).IsLeftAdjoint :=
  (pullbackSheafFunctorAdjunction f).isLeftAdjoint

/-- Direct image of commutative-ring sheaves along `f`, rewritten through spaces-étale
pullback. -/
def commRingPushforwardFactor {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    sheafPushforward CommRingCat.{u} f ≅
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous CommRingCat.{u}
          (spacesEtaleTopology W) (spacesEtaleTopology Y) ⋙
        (smallEtaleInclusion W).sheafPushforwardContinuous CommRingCat.{u}
          (smallEtaleTopology W) (spacesEtaleTopology W) :=
  isoWhiskerLeft
    ((smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y))
    ((Functor.sheafPushforwardContinuousIso
        (smallEtaleInclusion_comp_spacesEtalePullback f)
        CommRingCat.{u} (smallEtaleTopology W) (spacesEtaleTopology Y)).symm ≪≫
      Functor.sheafPushforwardContinuousComp (smallEtaleInclusion W) (spacesEtalePullback f)
        CommRingCat.{u} (smallEtaleTopology W) (spacesEtaleTopology W)
        (spacesEtaleTopology Y))

/-- Restricting a spaces étale commutative-ring sheaf to the small étale site and extending
it back is isomorphic to the identity. -/
def smallEtaleInclusionContinuousCocontinuousIso_commRing (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardContinuous CommRingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) CommRingCat.{u}) :=
  let restrict :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let extend :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous CommRingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous CommRingCat.{u}
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
      Functor.IsCoverDense.sheafIso i)
    sorry

/-- Continuous pushforward of commutative-ring sheaves along spaces-étale pullback respects
composition. -/
def spacesEtaleCommRingPushforwardComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    (spacesEtalePullback f).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology W) (spacesEtaleTopology Y) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology T) (spacesEtaleTopology W) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous CommRingCat.{u}
        (spacesEtaleTopology T) (spacesEtaleTopology Y) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f)
      CommRingCat.{u} (spacesEtaleTopology T) (spacesEtaleTopology W)
      (spacesEtaleTopology Y) ≪≫
    Functor.sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm
      CommRingCat.{u} (spacesEtaleTopology T) (spacesEtaleTopology Y)

/-- Direct image of commutative-ring sheaves along a composite is the composite of the
direct images. -/
def commRingPushforwardComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    commRingPushforward f ⋙ commRingPushforward g ≅ commRingPushforward (f ≫ g) :=

  AlgebraicGeometry.AlgebraicSpace.commRingPushforwardComp f g

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def commRingInverseImageComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    commRingInverseImage g ⋙ commRingInverseImage f ≅ commRingInverseImage (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (commRingInverseImageAdjunction g) (commRingInverseImageAdjunction f)
    (commRingInverseImageAdjunction (f ≫ g)) (commRingPushforwardComp f g)

/-- Restriction of commutative-ring sheaves along an étale morphism, by postcomposition
on small étale sites. -/
def restrictSheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    Sheaf (smallEtaleTopology W) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  (Modules.restrictPostcompose f).sheafPushforwardContinuous CommRingCat.{u}
    (smallEtaleTopology Y) (smallEtaleTopology W)

/-- Lift a type-valued map of forgotten ring sheaves to a morphism of ring sheaves. -/
def ringSheafHomOfTypeHom {Y : AlgebraicSpace S}
    {R S : Sheaf (smallEtaleTopology Y) RingCat.{u}}
    (φ : (sheafCompose (smallEtaleTopology Y) (CategoryTheory.forget RingCat.{u})).obj R ⟶
      (sheafCompose (smallEtaleTopology Y) (CategoryTheory.forget RingCat.{u})).obj S) :
    R ⟶ S :=
  ⟨{ app := fun U ↦
        ConcreteCategory.ofHom (C := RingCat.{u})
          { toFun := ((sheafToPresheaf (smallEtaleTopology Y) (Type u)).map φ).app U
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
     naturality := fun _ _ _ ↦ sorry }⟩

/-- Lift a type-valued isomorphism of forgotten ring sheaves to an isomorphism of ring sheaves. -/
def ringSheafIsoOfTypeIso {Y : AlgebraicSpace S}
    {R S : Sheaf (smallEtaleTopology Y) RingCat.{u}}
    (e : (sheafCompose (smallEtaleTopology Y) (CategoryTheory.forget RingCat.{u})).obj R ≅
      (sheafCompose (smallEtaleTopology Y) (CategoryTheory.forget RingCat.{u})).obj S) :
    R ≅ S where
  hom := ringSheafHomOfTypeHom e.hom
  inv := ringSheafHomOfTypeHom e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forgetting commutativity after the internal direct image recovers ring-valued direct image. -/
def pullbackSheafPushforward_forgetRingIso {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((pullbackSheafPushforward f).obj A) ≅
      (ringedToposHom f).toTopos.ringDirectImage.obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  Iso.refl _

/-- Ring-valued direct image of the internal construction agrees with site-theoretic
ring-valued direct image. -/
def ringDirectImageIsoRingPushforward {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (A : Sheaf (smallEtaleTopology Y) RingCat.{u}) :
    (ringedToposHom f).toTopos.ringDirectImage.obj A ≅ (ringPushforward f).obj A :=
  ringSheafIsoOfTypeIso
    (((ringedToposHom f).toTopos.ringDirectImageForgetIso.app A) ≪≫
      ((ringPushforwardForgetIso f).app A).symm)

/-- Site-theoretic commutative-ring pushforward agrees with `sheafPushforward`. -/
def commRingPushforwardIsoSheafPushforward {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    (sheafPushforward CommRingCat.{u} f).obj A ≅ (commRingPushforward f).obj A :=
  let u := smallEtaleInclusion Y
  let v := etaleBaseChange f
  let F := forget CommRingCat.{u}
  let Ju := smallEtaleTopology Y
  let Ku := spacesEtaleTopology Y
  let Jv := smallEtaleTopology W
  let e : sheafPushforward CommRingCat.{u} f ⋙ sheafCompose Jv F ≅
      sheafCompose Ju F ⋙ typePushforward f :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous CommRingCat.{u} Ju Ku)
        (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F Jv Ku)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.sheafPushforwardCocontinuous.compSheafComposeIso u F Ju Ku)
        (v.sheafPushforwardContinuous (Type u) Jv Ku) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (sheafCompose Ju F)
        (Functor.isoWhiskerRight
          (Adjunction.rightAdjointUniq (EtaleTopos.siteEquivalence Y).toAdjunction
            (u.sheafAdjunctionCocontinuous (Type u) Ju Ku)).symm
          (v.sheafPushforwardContinuous (Type u) Jv Ku))
  let c := e.app A ≪≫ ((commRingPushforwardUnderlyingIso f).app A).symm
  { hom := commRingHomOfUnderlying c.hom sorry sorry sorry sorry
    inv := commRingHomOfUnderlying c.inv sorry sorry sorry sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Ring-valued comparison of internal and site-theoretic direct images. -/
def pullbackSheafPushforwardForgetRingIso {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((pullbackSheafPushforward f).obj A) ≅
      (sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((commRingPushforward f).obj A) :=
  pullbackSheafPushforward_forgetRingIso f A ≪≫
    ringDirectImageIsoRingPushforward f
      ((sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ≪≫
    ((commRingPushforwardForget₂Iso f).app A).symm

/-- Forgotten type sheaf of étale restriction of a commutative-ring sheaf. -/
def etaleRestrictionForgetTypeIso {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (A : Sheaf (smallEtaleTopology W) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (((etaleRestriction f).sheafPushforwardContinuous CommRingCat.{u}
              (smallEtaleTopology Y) (smallEtaleTopology W)).obj A)) ≅
      ((etaleRestriction f).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology Y) (smallEtaleTopology W)).obj
        ((sheafCompose (smallEtaleTopology W) (forget RingCat.{u})).obj
          ((sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :=
  (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).mapIso
      (eqToIso (congrArg (fun G ↦ G.obj A)
        (Functor.sheafPushforwardContinuous.compSheafCompose
          (etaleRestriction f) (forget₂ CommRingCat.{u} RingCat.{u})
          (smallEtaleTopology Y) (smallEtaleTopology W)))) ≪≫
    eqToIso (congrArg (fun G ↦ G.obj
        ((sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
      (Functor.sheafPushforwardContinuous.compSheafCompose
        (etaleRestriction f) (forget RingCat.{u})
        (smallEtaleTopology Y) (smallEtaleTopology W)))

/-- The opposite of étale restriction has pointwise right Kan extensions on type-valued
presheaves. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension_type
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (etaleRestriction f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The opposite of spaces étale restriction has pointwise right Kan extensions on type-valued
presheaves. -/
instance spacesEtaleRestriction_op_hasPointwiseRightKanExtension_type
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (P : (spacesEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (spacesEtaleRestriction f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Spaces étale restriction is cocontinuous, as the left adjoint of continuous pullback. -/
instance spacesEtaleRestriction_isCocontinuous {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    (spacesEtaleRestriction f).IsCocontinuous (spacesEtaleTopology Y) (spacesEtaleTopology W) :=
  Functor.ContinuousRightAdjoint.left_isCocontinuous
    (spacesEtaleRestriction f) (spacesEtalePullback f)
    (MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ f inferInstance trivial)

/-- Small étale inclusion followed by spaces étale restriction is cocontinuous. -/
instance smallEtaleInclusion_comp_spacesEtaleRestriction_isCocontinuous
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    (smallEtaleInclusion Y ⋙ spacesEtaleRestriction f).IsCocontinuous
      (smallEtaleTopology Y) (spacesEtaleTopology W) :=
  isCocontinuous_comp (smallEtaleInclusion Y) (spacesEtaleRestriction f)
    (smallEtaleTopology Y) (spacesEtaleTopology Y)

/-- Étale restriction followed by the spaces inclusion is cocontinuous. -/
instance etaleRestriction_comp_smallEtaleInclusion_isCocontinuous
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    (etaleRestriction f ⋙ smallEtaleInclusion W).IsCocontinuous
      (smallEtaleTopology Y) (spacesEtaleTopology W) :=
  isCocontinuous_comp (etaleRestriction f) (smallEtaleInclusion W)
    (smallEtaleTopology Y) (smallEtaleTopology W)

/-- The opposite of the composite of small étale inclusion with spaces étale restriction has
pointwise right Kan extensions on type-valued presheaves. -/
instance inclusionRestriction_hasPointwiseRan
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (smallEtaleInclusion Y ⋙ spacesEtaleRestriction f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The opposite of the composite of étale restriction with the spaces inclusion has pointwise
right Kan extensions on type-valued presheaves. -/
instance restrictionInclusion_hasPointwiseRan
    {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (etaleRestriction f ⋙ smallEtaleInclusion W).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The counit of continuous restriction ⊣ cocontinuous extension along the small étale
inclusion is an isomorphism on small étale type sheaves. -/
instance instIsIso_smallEtaleInclusion_sheafAdjunctionCocontinuous_counit
    (Y : AlgebraicSpace S) (F : Sheaf (smallEtaleTopology Y) (Type u)) :
    IsIso (((smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).counit.app F) :=
  sorry

/-- Extending a small étale type sheaf to the spaces étale site and restricting it back is
isomorphic to the identity. -/
def smallEtaleInclusionCocontinuousContinuousIso (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (smallEtaleTopology Y) (Type u)) :=
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  NatIso.ofComponents (fun F ↦ asIso (adj.counit.app F)) sorry

/-- Direct image of type-valued sheaves along an étale morphism agrees with cocontinuous
pushforward of `etaleRestriction`. -/
def typePushforwardIsoEtaleCocontinuous {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    typePushforward f ≅
      (etaleRestriction f).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology Y) (smallEtaleTopology W) :=
  let iY :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let iWrestrict :=
    (smallEtaleInclusion W).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology W) (spacesEtaleTopology W)
  let rSpaces :=
    (spacesEtaleRestriction f).sheafPushforwardCocontinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology W)
  let iWextend :=
    (smallEtaleInclusion W).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology W) (spacesEtaleTopology W)
  let jCocont :=
    (etaleRestriction f).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Y) (smallEtaleTopology W)
  Modules.typePushforwardFactor f ≪≫
    isoWhiskerRight
      (Adjunction.rightAdjointUniq (EtaleTopos.siteEquivalence Y).toAdjunction
        ((smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology Y)))
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology W) (spacesEtaleTopology Y) ⋙ iWrestrict) ≪≫
    isoWhiskerLeft iY (isoWhiskerRight
      (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
        (spacesEtaleRestriction f) (spacesEtalePullback f) (Type u)
        (MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ f inferInstance trivial))
      iWrestrict) ≪≫
    (Functor.associator iY rSpaces iWrestrict).symm ≪≫
    isoWhiskerRight
      (sheafPushforwardCocontinuousComp' (smallEtaleTopology Y) (spacesEtaleTopology Y)
          (spacesEtaleTopology W) (smallEtaleInclusion Y) (spacesEtaleRestriction f)
          (etaleRestriction_comp_inclusion f).symm)
      iWrestrict ≪≫
    isoWhiskerRight
      (sheafPushforwardCocontinuousComp (smallEtaleTopology Y) (smallEtaleTopology W)
          (spacesEtaleTopology W) (etaleRestriction f) (smallEtaleInclusion W)).symm
      iWrestrict ≪≫
    Functor.associator jCocont iWextend iWrestrict ≪≫
    isoWhiskerLeft jCocont (smallEtaleInclusionCocontinuousContinuousIso W) ≪≫
    Functor.rightUnitor jCocont

/-- Étale restriction of type-valued sheaves agrees with inverse image along the associated
morphism of small étale topoi. -/
def etaleRestrictionTypeIsoInverseImage {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    (etaleRestriction f).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (smallEtaleTopology W) ≅
      (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    ((etaleRestriction f).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology Y) (smallEtaleTopology W))
    ((morphismOfTopoi f).adjunction.ofNatIsoRight (typePushforwardIsoEtaleCocontinuous f))

/-- Forgotten étale restriction of commutative-ring sheaves agrees with ring inverse image. -/
def etaleRestrictionSheafForgetRingIso {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (A : Sheaf (smallEtaleTopology W) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (((etaleRestriction f).sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleTopology Y) (smallEtaleTopology W)).obj A) ≅
      (ringedToposHom f).toTopos.ringInverseImage.obj
        ((sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  ringSheafIsoOfTypeIso
    (etaleRestrictionForgetTypeIso f A ≪≫
      (etaleRestrictionTypeIsoInverseImage f).app
        ((sheafCompose (smallEtaleTopology W) (forget RingCat.{u})).obj
          ((sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) ≪≫
      ((ringedToposHom f).toTopos.ringInverseImageForgetIso.app
          ((sheafCompose (smallEtaleTopology W) (forget₂ CommRingCat.{u} RingCat.{u})).obj A)).symm)

/-- Ring-valued comparison of étale restriction with internal inverse image. -/
def restrictSheafForgetRingIso {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f]
    (A : Sheaf (smallEtaleTopology W) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((restrictSheaf f).obj A) ≅
      (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((QcAlgebraUnder.pullbackSheafFunctor f).obj A) :=
  (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
      ((Functor.sheafPushforwardContinuousIso (Modules.restrictPostcomposeIso f)
          CommRingCat.{u} (smallEtaleTopology Y) (smallEtaleTopology W)).app A) ≪≫
    etaleRestrictionSheafForgetRingIso f A ≪≫
    (QcAlgebraUnder.pullbackSheafFunctor_forgetRingIso f A).symm

/-- Internal and site-theoretic direct images of commutative-ring sheaves agree
sectionwise. -/
def pullbackSheafPushforwardIso {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    pullbackSheafPushforward f ≅ commRingPushforward f :=
  NatIso.ofComponents
    (fun A ↦
      (CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u} (J := smallEtaleTopology W)).preimageIso
        (pullbackSheafPushforwardForgetRingIso f A))
    sorry

/-- The two inverse-image presentations of commutative-ring sheaves are canonically
isomorphic, as mates of the comparison of their direct images. -/
def pullbackSheafFunctorIso {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    QcAlgebraUnder.pullbackSheafFunctor f ≅ commRingInverseImage f :=
  ((conjugateIsoEquiv (pullbackSheafFunctorAdjunction f)
        (commRingInverseImageAdjunction f)).symm
      (pullbackSheafPushforwardIso f)).symm

/-- Étale restriction of commutative-ring sheaves is isomorphic to inverse image in the
algebra-pullback presentation. -/
def restrictSheafIsoPullbackSheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W) [Etale f] :
    restrictSheaf f ≅ QcAlgebraUnder.pullbackSheafFunctor f :=
  NatIso.ofComponents
    (fun A ↦
      (CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u} (J := smallEtaleTopology Y)).preimageIso
        (restrictSheafForgetRingIso f A))
    sorry

/-- Inverse image of commutative-ring sheaves in the algebra-pullback presentation
reassociates along composition. -/
def pullbackSheafFunctorComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    QcAlgebraUnder.pullbackSheafFunctor g ⋙ QcAlgebraUnder.pullbackSheafFunctor f ≅
      QcAlgebraUnder.pullbackSheafFunctor (f ≫ g) :=
  isoWhiskerRight (pullbackSheafFunctorIso g) (QcAlgebraUnder.pullbackSheafFunctor f) ≪≫
    isoWhiskerLeft (commRingInverseImage g) (pullbackSheafFunctorIso f) ≪≫
      commRingInverseImageComp f g ≪≫ (pullbackSheafFunctorIso (f ≫ g)).symm

/-- Inverse image of commutative-ring sheaves preserves pushouts, so the comparison is invertible. -/
instance instIsIso_pushoutComparison_pullbackSheafFunctor {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    {A B C : Sheaf (smallEtaleTopology W) CommRingCat.{u}}
    (h : A ⟶ B) (k : A ⟶ C) :
    IsIso (pushoutComparison (QcAlgebraUnder.pullbackSheafFunctor f) h k) :=
  sorry

/-- Forward sheaf of successive algebra pullbacks, compared with pullback along the composite. -/
def pullbackCompSheafHom {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((QcAlgebraUnder.pullback f).obj ((QcAlgebraUnder.pullback g).obj A)).obj.right ⟶
      ((QcAlgebraUnder.pullback (f ≫ g)).obj A).obj.right :=
  let F := QcAlgebraUnder.pullbackSheafFunctor f
  let Gfun := QcAlgebraUnder.pullbackSheafFunctor g
  let Fg := QcAlgebraUnder.pullbackSheafFunctor (f ≫ g)
  let inner := (QcAlgebraUnder.pullbackUnder g).obj A.obj
  let composite := (QcAlgebraUnder.pullbackUnder (f ≫ g)).obj A.obj
  pushout.desc
    ((asIso (pushoutComparison F (Gfun.map A.obj.hom)
          (QcAlgebraUnder.inverseImageStructure g))).inv ≫
      pushout.desc
        ((pullbackSheafFunctorComp f g).hom.app A.obj.right ≫
          pushout.inl (Fg.map A.obj.hom) (QcAlgebraUnder.inverseImageStructure (f ≫ g)))
        (QcAlgebraUnder.inverseImageStructure f ≫ composite.hom)
        sorry)
    composite.hom
    sorry

/-- Reverse sheaf of pullback along a composite, compared with successive algebra pullbacks. -/
def pullbackCompSheafInv {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((QcAlgebraUnder.pullback (f ≫ g)).obj A).obj.right ⟶
      ((QcAlgebraUnder.pullback f).obj ((QcAlgebraUnder.pullback g).obj A)).obj.right :=
  let F := QcAlgebraUnder.pullbackSheafFunctor f
  let Gfun := QcAlgebraUnder.pullbackSheafFunctor g
  let Fg := QcAlgebraUnder.pullbackSheafFunctor (f ≫ g)
  let inner := (QcAlgebraUnder.pullbackUnder g).obj A.obj
  let nested := (QcAlgebraUnder.pullbackUnder f).obj inner
  pushout.desc
    ((pullbackSheafFunctorComp f g).inv.app A.obj.right ≫
      F.map (pushout.inl (Gfun.map A.obj.hom) (QcAlgebraUnder.inverseImageStructure g)) ≫
        pushout.inl (F.map inner.hom) (QcAlgebraUnder.inverseImageStructure f))
    nested.hom
    sorry

/-- The sheaf comparison of successive algebra pullbacks commutes with structure maps. -/
theorem pullbackCompSheafHom_w {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((QcAlgebraUnder.pullback f).obj ((QcAlgebraUnder.pullback g).obj A)).obj.hom ≫
        pullbackCompSheafHom f g A =
      ((QcAlgebraUnder.pullback (f ≫ g)).obj A).obj.hom :=
  sorry

/-- The reverse sheaf comparison of successive algebra pullbacks commutes with structure maps. -/
theorem pullbackCompSheafInv_w {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T)
    (A : T.QcAlgebraUnder) :
    ((QcAlgebraUnder.pullback (f ≫ g)).obj A).obj.hom ≫ pullbackCompSheafInv f g A =
      ((QcAlgebraUnder.pullback f).obj ((QcAlgebraUnder.pullback g).obj A)).obj.hom :=
  sorry

/-- Composition of algebra pullbacks identifies with pullback along the composite. -/
def pullbackComp {Y W T : AlgebraicSpace S} (f : Y ⟶ W) (g : W ⟶ T) :
    QcAlgebraUnder.pullback g ⋙ QcAlgebraUnder.pullback f ≅
      QcAlgebraUnder.pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun A ↦
      { hom :=
          homMk (Under.homMk (pullbackCompSheafHom f g A) (pullbackCompSheafHom_w f g A))
        inv :=
          homMk (Under.homMk (pullbackCompSheafInv f g A) (pullbackCompSheafInv_w f g A))
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
variable {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]

/-- Pullback of an étale morphism along the coborder open is étale. -/
instance instEtale_coborderFst :
    Etale (pullback.fst (IsImmersion.coborderRange i).ι φ) :=
  sorry

/-- The coborder comparison of `ι` with the pulled coborder of `i` is étale. -/
instance instEtale_coborderToPullback :
    Etale (Hom.Conormal.coborderToPullback i φ) :=
  sorry

/-- Forward sheaf identifying the coborder-algebra pullback with `total i`. -/
def totalIsoSheafHom :
    ((QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i)).obj.right ⟶
      (total i).obj.right :=
  pushout.desc
    ((pullbackSheafFunctorIso (IsImmersion.liftCoborder i)).hom.app (coborderGradeSheaf i) ≫
      totalInr i)
    (structureMap i)
    sorry

/-- Reverse sheaf identifying `total i` with the coborder-algebra pullback. -/
def totalIsoSheafInv :
    (total i).obj.right ⟶
      ((QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i)).obj.right :=
  pushout.desc
    ((QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i)).obj.hom
    ((pullbackSheafFunctorIso (IsImmersion.liftCoborder i)).inv.app (coborderGradeSheaf i) ≫
      pushout.inl
        ((QcAlgebraUnder.pullbackSheafFunctor (IsImmersion.liftCoborder i)).map
          (coborderStructureMap i))
        (QcAlgebraUnder.inverseImageStructure (IsImmersion.liftCoborder i)))
    sorry

/-- The coborder-algebra pullback comparison commutes with structure maps. -/
theorem totalIsoSheafHom_w :
    ((QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i)).obj.hom ≫
        totalIsoSheafHom i =
      (total i).obj.hom :=
  sorry

/-- Identification of `total i` with the coborder-algebra pullback along `liftCoborder i`. -/
theorem totalIsoSheafInv_w :
    (total i).obj.hom ≫ totalIsoSheafInv i =
      ((QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i)).obj.hom :=
  sorry

/-- Identification of `total i` with the coborder-algebra pullback along `liftCoborder i`. -/
def totalIso :
    (QcAlgebraUnder.pullback (IsImmersion.liftCoborder i)).obj (coborderTotal i) ≅
      total i where
  hom := homMk (Under.homMk (totalIsoSheafHom i) (totalIsoSheafHom_w i))
  inv := homMk (Under.homMk (totalIsoSheafInv i) (totalIsoSheafInv_w i))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Kernel map `𝒪_X ⟶ f_* 𝒪_Z` of a morphism of algebraic spaces. -/
def kernelMap {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    commRingStructureSheaf W ⟶
      (commRingPushforward f).obj (commRingStructureSheaf Y) :=
  commRingStructureSheafMap f

/-- Restriction of sections carries one kernel ideal into the next. -/
theorem kernel_sectionIdeal_le_comap {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    {V V' : (smallEtaleSite W)ᵒᵖ} (h : V ⟶ V') :
    KernelIdeal.sectionIdeal (kernelMap f) V ≤
      Ideal.comap (((commRingStructureSheaf W).obj.map h).hom)
        (KernelIdeal.sectionIdeal (kernelMap f) V') :=
  sorry

/-- Sectionwise associated graded ring of the kernel ideal of `f`. -/
def gradeObj {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (V : (smallEtaleSite W)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (kernelMap f) V))

/-- Restriction of the sectionwise associated graded rings of the kernel of `f`. -/
def gradeMap {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    {V V' : (smallEtaleSite W)ᵒᵖ} (h : V ⟶ V') :
    gradeObj f V ⟶ gradeObj f V' :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map
      (((commRingStructureSheaf W).obj.map h).hom)
      (kernel_sectionIdeal_le_comap f h))

/-- The associated graded of the kernel of `f` as a presheaf of commutative rings. -/
def gradePresheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    (smallEtaleSite W)ᵒᵖ ⥤ CommRingCat.{u} where
  obj := gradeObj f
  map := gradeMap f
  map_id := sorry
  map_comp := sorry

/-- The associated graded of the kernel of `f`, sheafified on the small étale site of
the target. -/
def gradeSheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    Sheaf (smallEtaleTopology W) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology W) CommRingCat.{u}).obj (gradePresheaf f)

/-- The component at `V` of the associated graded structure map of `f`. -/
def gradeStructureMap_app {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    (V : (smallEtaleSite W)ᵒᵖ) :
    (commRingStructureSheaf W).obj.obj V ⟶ gradeObj f V :=
  CommRingCat.ofHom
    (algebraMap
      ((commRingStructureSheaf W).obj.obj V)
      (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (kernelMap f) V)))

/-- The associated graded structure map of `f` as a morphism of presheaves. -/
def gradeStructureMapPresheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    (commRingStructureSheaf W).obj ⟶ gradePresheaf f where
  app V := gradeStructureMap_app f V
  naturality := fun _ _ _ => sorry

/-- The structure map from `𝒪_X` to the sheafified associated graded of the kernel of
`f`. -/
def gradeStructureMap {Y W : AlgebraicSpace S} (f : Y ⟶ W) :
    commRingStructureSheaf W ⟶ gradeSheaf f :=
  CategoryTheory.Sheaf.homEquiv.symm
    (gradeStructureMapPresheaf f ≫
      toSheafify (smallEtaleTopology W) (gradePresheaf f))

/-- The associated graded `𝒪_X`-algebra of a closed immersion `f : Z ⟶ X`. -/
def closedImmersionTotal {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    [IsClosedImmersion f] : W.QcAlgebraUnder where
  obj := Under.mk (gradeStructureMap f)
  property := sorry

/-- The sheaf of `closedImmersionTotal f` is the sheafified associated graded of the
kernel of `f`. -/
theorem closedImmersionTotal_sheaf {Y W : AlgebraicSpace S} (f : Y ⟶ W)
    [IsClosedImmersion f] :
    (closedImmersionTotal f).obj.right = gradeSheaf f :=
  rfl

/-- The structure sheaf map of `p : coborderPullback ⟶ coborder i` carries the coborder
kernel of `i` into the kernel of `liftToCoborder`. -/
theorem coborderGrade_le_comap_lift
    (V : smallEtaleSite (Hom.coborder i))
    (a : StructuredArrow (op ((etaleBaseChange
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj V))
      (smallEtaleInclusion (Hom.Conormal.coborderPullback i φ)).op) :
    KernelIdeal.sectionIdeal (coborderKernelMap i) (op V) ≤
      Ideal.comap
        ((etaleSquareOfArrow
            (pullback.fst (IsImmersion.coborderRange i).ι φ) V a).map.left.appTop).hom
        (KernelIdeal.sectionIdeal (kernelMap (Hom.Conormal.liftToCoborder i φ))
          a.right) :=
  sorry

/-- Associated-graded component of an étale square, before sheafification. -/
def coborderGradeToObj
    (V : smallEtaleSite (Hom.coborder i))
    (a : StructuredArrow (op ((etaleBaseChange
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj V))
      (smallEtaleInclusion (Hom.Conormal.coborderPullback i φ)).op) :
    coborderGradeObj i (op V) ⟶
      gradeObj (Hom.Conormal.liftToCoborder i φ) a.right :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map
      ((etaleSquareOfArrow
          (pullback.fst (IsImmersion.coborderRange i).ι φ) V a).map.left.appTop).hom
      (coborderGrade_le_comap_lift i φ V a))

/-- Cone of associated-graded maps presenting
`C_{Z/X,*}|_{X \ ∂Z}` along `U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeToPushforwardCone (V : smallEtaleSite (Hom.coborder i)) :
    Cone
      (StructuredArrow.proj
        (op ((etaleBaseChange
            (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj V))
        (smallEtaleInclusion (Hom.Conormal.coborderPullback i φ)).op ⋙
          (gradeSheaf (Hom.Conormal.liftToCoborder i φ)).obj) where
  pt := coborderGradeObj i (op V)
  π :=
    { app := fun a ↦
        coborderGradeToObj i φ V a ≫
          (toSheafify (smallEtaleTopology (Hom.Conormal.coborderPullback i φ))
              (gradePresheaf (Hom.Conormal.liftToCoborder i φ))).app a.right
      naturality := fun _ _ _ ↦ sorry }

/-- Component at `V` of the pushforward comparison of coborder associated graded
algebras along `pullback.fst`. -/
def coborderGradeToPushforwardApp (V : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    coborderGradeObj i V ⟶
      ((commRingPushforward
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).obj.obj V :=

  commRingPushforwardConeLift (pullback.fst (IsImmersion.coborderRange i).ι φ)
    (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) V.unop
    (coborderGradeToPushforwardCone i φ V.unop)

/-- Presheaf comparison of coborder associated graded algebras along
`U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeToPushforwardPresheaf :
    coborderGradePresheaf i ⟶
      ((commRingPushforward
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).obj where
  app := coborderGradeToPushforwardApp i φ
  naturality := fun _ _ _ ↦ sorry

/-- Pushforward comparison `C_{Z/X,*}` of coborder associated graded algebras along
`U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeToPushforward :
    coborderGradeSheaf i ⟶
      (commRingPushforward
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.coborder i))
      (coborderGradeToPushforwardPresheaf i φ)
      ((commRingPushforward
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).property⟩

/-- Inverse-image comparison of coborder associated graded algebras along
`pullback.fst`, obtained by adjunction from `coborderGradeToPushforward`. -/
def coborderGradeRestrictSheaf :
    (commRingInverseImage
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
      (coborderGradeSheaf i) ⟶
      gradeSheaf (Hom.Conormal.liftToCoborder i φ) :=

  ((commRingInverseImageAdjunction
    (pullback.fst (IsImmersion.coborderRange i).ι φ)).homEquiv _ _).symm
      (coborderGradeToPushforward i φ)

/-- The pulled coborder associated graded of `i` maps to the associated graded of
`liftToCoborder` after scalar extension to `𝒪_{U \ φ⁻¹(∂Z)}`. -/
theorem coborderGradeRestrict_w :
    (QcAlgebraUnder.pullbackSheafFunctor
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
        (coborderStructureMap i) ≫
      (pullbackSheafFunctorIso
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).hom.app
        (coborderGradeSheaf i) ≫
        coborderGradeRestrictSheaf i φ =
      QcAlgebraUnder.inverseImageStructure
          (pullback.fst (IsImmersion.coborderRange i).ι φ) ≫
        gradeStructureMap (Hom.Conormal.liftToCoborder i φ) :=
  sorry

/-- Right-hand sheaf of the coborder associated-graded comparison along
`pullback.fst`. -/
def coborderGradeRestrictRight :
    ((QcAlgebraUnder.pullback
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderTotal i)).obj.right ⟶
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)).obj.right :=
  pushout.desc
    ((pullbackSheafFunctorIso
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).hom.app
        (coborderGradeSheaf i) ≫
      coborderGradeRestrictSheaf i φ)
    (gradeStructureMap (Hom.Conormal.liftToCoborder i φ))
    (coborderGradeRestrict_w i φ)

/-- The coborder associated-graded comparison along `pullback.fst` commutes with
structure maps. -/
theorem coborderGradeRestrictRight_w :
    ((QcAlgebraUnder.pullback
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderTotal i)).obj.hom ≫
      coborderGradeRestrictRight i φ =
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)).obj.hom :=
  sorry

/-- Comparison of coborder associated graded algebras along
`U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeRestrict :
    (QcAlgebraUnder.pullback
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
      (coborderTotal i) ⟶
      closedImmersionTotal (Hom.Conormal.liftToCoborder i φ) :=
  homMk (Under.homMk (coborderGradeRestrictRight i φ) (coborderGradeRestrictRight_w i φ))

/-- The structure sheaf map of `coborderToPullback` carries the kernel of
`liftToCoborder` into the coborder kernel of `ι`. -/
theorem liftGrade_le_comap_ι
    (V : smallEtaleSite (Hom.Conormal.coborderPullback i φ))
    (a : StructuredArrow (op ((etaleBaseChange (Hom.Conormal.coborderToPullback i φ)).obj V))
      (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op) :
    KernelIdeal.sectionIdeal (kernelMap (Hom.Conormal.liftToCoborder i φ)) (op V) ≤
      Ideal.comap
        ((etaleSquareOfArrow (Hom.Conormal.coborderToPullback i φ) V a).map.left.appTop).hom
        (KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i φ)) a.right) :=
  sorry

/-- Associated-graded component of `coborderToPullback`, before sheafification. -/
def coborderιGradeToObj
    (V : smallEtaleSite (Hom.Conormal.coborderPullback i φ))
    (a : StructuredArrow (op ((etaleBaseChange (Hom.Conormal.coborderToPullback i φ)).obj V))
      (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op) :
    gradeObj (Hom.Conormal.liftToCoborder i φ) (op V) ⟶
      coborderGradeObj (Hom.Conormal.ι i φ) a.right :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map
      ((etaleSquareOfArrow (Hom.Conormal.coborderToPullback i φ) V a).map.left.appTop).hom
      (liftGrade_le_comap_ι i φ V a))

/-- Cone of associated-graded maps presenting the coborder-`ι` comparison along
`coborderToPullback`. -/
def coborderιGradeToPushforwardCone
    (V : smallEtaleSite (Hom.Conormal.coborderPullback i φ)) :
    Cone
      (StructuredArrow.proj
        (op ((etaleBaseChange (Hom.Conormal.coborderToPullback i φ)).obj V))
        (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op ⋙
          (coborderGradeSheaf (Hom.Conormal.ι i φ)).obj) where
  pt := gradeObj (Hom.Conormal.liftToCoborder i φ) (op V)
  π :=
    { app := fun a ↦
        coborderιGradeToObj i φ V a ≫
          (toSheafify (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i φ)))
              (coborderGradePresheaf (Hom.Conormal.ι i φ))).app a.right
      naturality := fun _ _ _ ↦ sorry }

/-- Component at `V` of the pushforward comparison of associated graded algebras along
`coborderToPullback`. -/
def coborderιGradeToPushforwardApp
    (V : (smallEtaleSite (Hom.Conormal.coborderPullback i φ))ᵒᵖ) :
    gradeObj (Hom.Conormal.liftToCoborder i φ) V ⟶
      ((commRingPushforward (Hom.Conormal.coborderToPullback i φ)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).obj.obj V :=

  commRingPushforwardConeLift (Hom.Conormal.coborderToPullback i φ)
    (coborderGradeSheaf (Hom.Conormal.ι i φ)) V.unop
    (coborderιGradeToPushforwardCone i φ V.unop)

/-- Presheaf comparison of associated graded algebras along `coborderToPullback`. -/
def coborderιGradeToPushforwardPresheaf :
    gradePresheaf (Hom.Conormal.liftToCoborder i φ) ⟶
      ((commRingPushforward (Hom.Conormal.coborderToPullback i φ)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).obj where
  app := coborderιGradeToPushforwardApp i φ
  naturality := fun _ _ _ ↦ sorry

/-- Pushforward comparison of associated graded algebras along `coborderToPullback`. -/
def coborderιGradeToPushforward :
    gradeSheaf (Hom.Conormal.liftToCoborder i φ) ⟶
      (commRingPushforward (Hom.Conormal.coborderToPullback i φ)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ)) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.Conormal.coborderPullback i φ))
      (coborderιGradeToPushforwardPresheaf i φ)
      ((commRingPushforward (Hom.Conormal.coborderToPullback i φ)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).property⟩

/-- Inverse-image comparison of associated graded algebras along `coborderToPullback`. -/
def coborderιGradeRestrictSheaf :
    (commRingInverseImage (Hom.Conormal.coborderToPullback i φ)).obj
      (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) ⟶
      coborderGradeSheaf (Hom.Conormal.ι i φ) :=

  ((commRingInverseImageAdjunction (Hom.Conormal.coborderToPullback i φ)).homEquiv _ _).symm
    (coborderιGradeToPushforward i φ)

/-- The pulled associated graded of `liftToCoborder` maps to the coborder associated
graded of `ι` after scalar extension to `𝒪_{U \ φ⁻¹(∂Z)}` of `ι`. -/
theorem coborderιGradeRestrict_w :
    (QcAlgebraUnder.pullbackSheafFunctor (Hom.Conormal.coborderToPullback i φ)).map
        (gradeStructureMap (Hom.Conormal.liftToCoborder i φ)) ≫
      (pullbackSheafFunctorIso
          (Hom.Conormal.coborderToPullback i φ)).hom.app
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) ≫
        coborderιGradeRestrictSheaf i φ =
      QcAlgebraUnder.inverseImageStructure (Hom.Conormal.coborderToPullback i φ) ≫
        coborderStructureMap (Hom.Conormal.ι i φ) :=
  sorry

/-- Right-hand sheaf of the coborder-`ι` associated-graded comparison along
`coborderToPullback`. -/
def coborderιGradeRestrictRight :
    ((QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
        (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ))).obj.right ⟶
      (coborderTotal (Hom.Conormal.ι i φ)).obj.right :=
  pushout.desc
    ((pullbackSheafFunctorIso
          (Hom.Conormal.coborderToPullback i φ)).hom.app
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) ≫
      coborderιGradeRestrictSheaf i φ)
    (coborderStructureMap (Hom.Conormal.ι i φ))
    (coborderιGradeRestrict_w i φ)

/-- The coborder-`ι` associated-graded comparison commutes with structure maps. -/
theorem coborderιGradeRestrictRight_w :
    ((QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
        (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ))).obj.hom ≫
      coborderιGradeRestrictRight i φ =
      (coborderTotal (Hom.Conormal.ι i φ)).obj.hom :=
  sorry

/-- Comparison of associated graded algebras of `ι` along `coborderToPullback`. -/
def coborderιGradeRestrict :
    (QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ⟶
      coborderTotal (Hom.Conormal.ι i φ) :=
  homMk (Under.homMk (coborderιGradeRestrictRight i φ) (coborderιGradeRestrictRight_w i φ))

/-- The kernel of `liftToCoborder` is contained in the coborder kernel of `i` after
identifying sections along étale postcomposition. -/
theorem coborderGrade_le_comap_inv
    (W : (smallEtaleSite (Hom.Conormal.coborderPullback i φ))ᵒᵖ) :
    KernelIdeal.sectionIdeal (kernelMap (Hom.Conormal.liftToCoborder i φ)) W ≤
      Ideal.comap (RingHom.id _)
        (KernelIdeal.sectionIdeal (coborderKernelMap i)
          (op ((Modules.restrictPostcompose
              (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj W.unop))) :=
  sorry

/-- Reverse associated-graded map on sections along étale postcomposition. -/
def coborderGradeRestrictInvToObj
    (W : (smallEtaleSite (Hom.Conormal.coborderPullback i φ))ᵒᵖ) :
    gradeObj (Hom.Conormal.liftToCoborder i φ) W ⟶
      coborderGradeObj i
        (op ((Modules.restrictPostcompose
            (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj W.unop)) :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (RingHom.id _)
      (coborderGrade_le_comap_inv i φ W))

/-- Component at `W` of the reverse coborder associated-graded comparison along
`pullback.fst`. -/
def coborderGradeRestrictInvApp
    (W : (smallEtaleSite (Hom.Conormal.coborderPullback i φ))ᵒᵖ) :
    gradeObj (Hom.Conormal.liftToCoborder i φ) W ⟶
      ((restrictSheaf
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderGradeSheaf i)).obj.obj W :=
  coborderGradeRestrictInvToObj i φ W ≫
    (toSheafify (smallEtaleTopology (Hom.coborder i)) (coborderGradePresheaf i)).app
      (op ((Modules.restrictPostcompose
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj W.unop))

/-- Presheaf reverse comparison of coborder associated graded algebras along
`U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeRestrictInvPresheaf :
    gradePresheaf (Hom.Conormal.liftToCoborder i φ) ⟶
      ((restrictSheaf
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderGradeSheaf i)).obj where
  app := coborderGradeRestrictInvApp i φ
  naturality := fun _ _ _ ↦ sorry

/-- Sheaf reverse comparison of coborder associated graded algebras along étale
restriction. -/
def coborderGradeRestrictInvSheaf :
    gradeSheaf (Hom.Conormal.liftToCoborder i φ) ⟶
      (restrictSheaf
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderGradeSheaf i) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.Conormal.coborderPullback i φ))
      (coborderGradeRestrictInvPresheaf i φ)
      ((restrictSheaf
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderGradeSheaf i)).property⟩

/-- Reverse sheaf of the coborder associated-graded comparison after scalar extension. -/
def coborderGradeRestrictInvRight :
    (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)).obj.right ⟶
      ((QcAlgebraUnder.pullback
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderTotal i)).obj.right :=
  coborderGradeRestrictInvSheaf i φ ≫
    (restrictSheafIsoPullbackSheaf
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).hom.app
      (coborderGradeSheaf i) ≫
    pushout.inl
      ((QcAlgebraUnder.pullbackSheafFunctor
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).map
        (coborderStructureMap i))
      (QcAlgebraUnder.inverseImageStructure
        (pullback.fst (IsImmersion.coborderRange i).ι φ))

/-- The reverse coborder associated-graded comparison commutes with structure maps. -/
theorem coborderGradeRestrictInvRight_w :
    (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)).obj.hom ≫
      coborderGradeRestrictInvRight i φ =
      ((QcAlgebraUnder.pullback
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderTotal i)).obj.hom :=
  sorry

/-- Reverse comparison of coborder associated graded algebras along
`U \ φ⁻¹(∂Z) ⟶ X \ ∂Z`. -/
def coborderGradeRestrictInv :
    closedImmersionTotal (Hom.Conormal.liftToCoborder i φ) ⟶
      (QcAlgebraUnder.pullback
          (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
        (coborderTotal i) :=
  homMk (Under.homMk (coborderGradeRestrictInvRight i φ)
    (coborderGradeRestrictInvRight_w i φ))

/-- Identification of the pulled coborder associated graded of `i` with the associated
graded of `liftToCoborder`. -/
def coborderGradeRestrictIso :
    (QcAlgebraUnder.pullback
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).obj
      (coborderTotal i) ≅
      closedImmersionTotal (Hom.Conormal.liftToCoborder i φ) where
  hom := coborderGradeRestrict i φ
  inv := coborderGradeRestrictInv i φ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The coborder kernel of `ι` is contained in the kernel of `liftToCoborder` after
identifying sections along étale postcomposition. -/
theorem liftGrade_le_comap_ι_inv
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i φ)) W ≤
      Ideal.comap (RingHom.id _)
        (KernelIdeal.sectionIdeal (kernelMap (Hom.Conormal.liftToCoborder i φ))
          (op ((Modules.restrictPostcompose
              (Hom.Conormal.coborderToPullback i φ)).obj W.unop))) :=
  sorry

/-- Reverse associated-graded map on sections along `coborderToPullback`. -/
def coborderιGradeRestrictInvToObj
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    coborderGradeObj (Hom.Conormal.ι i φ) W ⟶
      gradeObj (Hom.Conormal.liftToCoborder i φ)
        (op ((Modules.restrictPostcompose
            (Hom.Conormal.coborderToPullback i φ)).obj W.unop)) :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (RingHom.id _)
      (liftGrade_le_comap_ι_inv i φ W))

/-- Component at `W` of the reverse coborder-`ι` associated-graded comparison. -/
def coborderιGradeRestrictInvApp
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    coborderGradeObj (Hom.Conormal.ι i φ) W ⟶
      ((restrictSheaf (Hom.Conormal.coborderToPullback i φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).obj.obj W :=
  coborderιGradeRestrictInvToObj i φ W ≫
    (toSheafify (smallEtaleTopology (Hom.Conormal.coborderPullback i φ))
        (gradePresheaf (Hom.Conormal.liftToCoborder i φ))).app
      (op ((Modules.restrictPostcompose
          (Hom.Conormal.coborderToPullback i φ)).obj W.unop))

/-- Presheaf reverse comparison of associated graded algebras along `coborderToPullback`. -/
def coborderιGradeRestrictInvPresheaf :
    coborderGradePresheaf (Hom.Conormal.ι i φ) ⟶
      ((restrictSheaf (Hom.Conormal.coborderToPullback i φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).obj where
  app := coborderιGradeRestrictInvApp i φ
  naturality := fun _ _ _ ↦ sorry

/-- Sheaf reverse comparison of associated graded algebras along étale restriction. -/
def coborderιGradeRestrictInvSheaf :
    coborderGradeSheaf (Hom.Conormal.ι i φ) ⟶
      (restrictSheaf (Hom.Conormal.coborderToPullback i φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i φ)))
      (coborderιGradeRestrictInvPresheaf i φ)
      ((restrictSheaf (Hom.Conormal.coborderToPullback i φ)).obj
        (gradeSheaf (Hom.Conormal.liftToCoborder i φ))).property⟩

/-- Reverse sheaf of the coborder-`ι` associated-graded comparison after scalar extension. -/
def coborderιGradeRestrictInvRight :
    (coborderTotal (Hom.Conormal.ι i φ)).obj.right ⟶
      ((QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
        (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ))).obj.right :=
  coborderιGradeRestrictInvSheaf i φ ≫
    (restrictSheafIsoPullbackSheaf
        (Hom.Conormal.coborderToPullback i φ)).hom.app
      (gradeSheaf (Hom.Conormal.liftToCoborder i φ)) ≫
    pushout.inl
      ((QcAlgebraUnder.pullbackSheafFunctor
          (Hom.Conormal.coborderToPullback i φ)).map
        (gradeStructureMap (Hom.Conormal.liftToCoborder i φ)))
      (QcAlgebraUnder.inverseImageStructure (Hom.Conormal.coborderToPullback i φ))

/-- The reverse coborder-`ι` associated-graded comparison commutes with structure maps. -/
theorem coborderιGradeRestrictInvRight_w :
    (coborderTotal (Hom.Conormal.ι i φ)).obj.hom ≫
      coborderιGradeRestrictInvRight i φ =
      ((QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
        (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ))).obj.hom :=
  sorry

/-- Reverse comparison of associated graded algebras of `ι` along `coborderToPullback`. -/
def coborderιGradeRestrictInv :
    coborderTotal (Hom.Conormal.ι i φ) ⟶
      (QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
        (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) :=
  homMk (Under.homMk (coborderιGradeRestrictInvRight i φ)
    (coborderιGradeRestrictInvRight_w i φ))

/-- Identification of the pulled associated graded of `liftToCoborder` with the coborder
associated graded of `ι`. -/
def coborderιGradeRestrictIso :
    (QcAlgebraUnder.pullback (Hom.Conormal.coborderToPullback i φ)).obj
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ≅
      coborderTotal (Hom.Conormal.ι i φ) where
  hom := coborderιGradeRestrict i φ
  inv := coborderιGradeRestrictInv i φ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forward comparison `C_{Z/X,*}|_{Z_U} ⟶ C_{Z_U/U,*}` induced by coborder pullback of
associated graded algebras. -/
def restrictEtaleHom :
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) ⟶
      total (Hom.Conormal.ι i φ) :=
  (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).map (totalIso i).inv ≫
    (pullbackComp (Hom.Conormal.toZ i φ) (IsImmersion.liftCoborder i)).hom.app
      (coborderTotal i) ≫
    (pullbackCongr (Hom.Conormal.coborderSq_w i φ)).hom.app (coborderTotal i) ≫
    (pullbackComp (Hom.Conormal.liftToCoborder i φ)
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).inv.app (coborderTotal i) ≫
    (QcAlgebraUnder.pullback (Hom.Conormal.liftToCoborder i φ)).map
      (coborderGradeRestrict i φ) ≫
    (pullbackCongr (Hom.Conormal.liftCoborder_ι_comp i φ).symm).hom.app
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ≫
    (pullbackComp (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))
        (Hom.Conormal.coborderToPullback i φ)).inv.app
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ≫
    (QcAlgebraUnder.pullback (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))).map
      (coborderιGradeRestrict i φ) ≫
    (totalIso (Hom.Conormal.ι i φ)).hom

/-- Inverse comparison `C_{Z_U/U,*} ⟶ C_{Z/X,*}|_{Z_U}` induced by coborder pullback of
associated graded algebras. -/
def restrictEtaleInv :
    total (Hom.Conormal.ι i φ) ⟶
      (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) :=
  (totalIso (Hom.Conormal.ι i φ)).inv ≫
    (QcAlgebraUnder.pullback (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))).map
      (coborderιGradeRestrictInv i φ) ≫
    (pullbackComp (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))
        (Hom.Conormal.coborderToPullback i φ)).hom.app
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ≫
    (pullbackCongr (Hom.Conormal.liftCoborder_ι_comp i φ).symm).inv.app
      (closedImmersionTotal (Hom.Conormal.liftToCoborder i φ)) ≫
    (QcAlgebraUnder.pullback (Hom.Conormal.liftToCoborder i φ)).map
      (coborderGradeRestrictInv i φ) ≫
    (pullbackComp (Hom.Conormal.liftToCoborder i φ)
        (pullback.fst (IsImmersion.coborderRange i).ι φ)).hom.app (coborderTotal i) ≫
    (pullbackCongr (Hom.Conormal.coborderSq_w i φ)).inv.app (coborderTotal i) ≫
    (pullbackComp (Hom.Conormal.toZ i φ) (IsImmersion.liftCoborder i)).inv.app
      (coborderTotal i) ≫
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).map (totalIso i).hom

/-- Canonical identification `C_{Z/X,*}|_{Z_U} ≅ C_{Z_U/U,*}` of quasi-coherent
`𝒪_{Z_U}`-algebras. -/
def restrictEtale :
    (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) ≅
      total (Hom.Conormal.ι i φ) where
  hom := restrictEtaleHom i φ
  inv := restrictEtaleInv i φ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `restrictEtale` is `restrictEtaleHom`. -/
@[simp]
theorem restrictEtale_hom :
    (restrictEtale i φ).hom = restrictEtaleHom i φ :=
  rfl

/-- The inverse component of `restrictEtale` is `restrictEtaleInv`. -/
@[simp]
theorem restrictEtale_inv :
    (restrictEtale i φ).inv = restrictEtaleInv i φ :=
  rfl

/-- Reassociation of successive algebra pullbacks of `C_{Z/X,*}` along `spaceMap` and
`toZ`. -/
def restrictEtaleToZReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).obj
        ((QcAlgebraUnder.pullback (Hom.Conormal.toZ i ψ)).obj (total i)) ≅
      (QcAlgebraUnder.pullback (Hom.Conormal.toZ i φ)).obj (total i) :=
  (pullbackComp (Hom.Conormal.spaceMap i φ ψ f hf) (Hom.Conormal.toZ i ψ)).app (total i) ≪≫
    (pullbackCongr (Hom.Conormal.spaceMap_comp_toZ i φ ψ f hf)).app (total i)

/-- The coborder morphism of étale charts is étale. -/
instance instEtale_chartCoborderHom {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    Etale (Hom.Conormal.chartCoborderHom i φ ψ f hf) :=
  sorry

/-- The coborder kernel of `ι i ψ` is carried into the coborder kernel of `ι i φ`
along `chartCoborderHom`. -/
theorem chartGrade_le_comap {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : smallEtaleSite (Hom.coborder (Hom.Conormal.ι i ψ)))
    (a : StructuredArrow
      (op ((etaleBaseChange (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W))
      (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op) :
    KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i ψ)) (op W) ≤
      Ideal.comap
        ((etaleSquareOfArrow (Hom.Conormal.chartCoborderHom i φ ψ f hf) W a).map.left.appTop).hom
        (KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i φ)) a.right) :=
  sorry

/-- Cone of associated-graded maps presenting the chart coborder comparison. -/
def chartGradeToObj {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : smallEtaleSite (Hom.coborder (Hom.Conormal.ι i ψ)))
    (a : StructuredArrow
      (op ((etaleBaseChange (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W))
      (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op) :
    coborderGradeObj (Hom.Conormal.ι i ψ) (op W) ⟶
      coborderGradeObj (Hom.Conormal.ι i φ) a.right :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map
      ((etaleSquareOfArrow (Hom.Conormal.chartCoborderHom i φ ψ f hf) W a).map.left.appTop).hom
      (chartGrade_le_comap i φ ψ f hf W a))

/-- Cone of associated-graded maps presenting the chart coborder comparison. -/
def chartGradeToPushforwardCone {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : smallEtaleSite (Hom.coborder (Hom.Conormal.ι i ψ))) :
    Cone
      (StructuredArrow.proj
        (op ((etaleBaseChange (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W))
        (smallEtaleInclusion (Hom.coborder (Hom.Conormal.ι i φ))).op ⋙
          (coborderGradeSheaf (Hom.Conormal.ι i φ)).obj) where
  pt := coborderGradeObj (Hom.Conormal.ι i ψ) (op W)
  π :=
    { app := fun a ↦
        chartGradeToObj i φ ψ f hf W a ≫
          (toSheafify (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i φ)))
              (coborderGradePresheaf (Hom.Conormal.ι i φ))).app a.right
      naturality := fun _ _ _ ↦ sorry }

/-- Component at `W` of the pushforward chart coborder associated-graded comparison. -/
def chartGradeToPushforwardApp {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i ψ)))ᵒᵖ) :
    coborderGradeObj (Hom.Conormal.ι i ψ) W ⟶
      ((commRingPushforward (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).obj.obj W :=

  commRingPushforwardConeLift (Hom.Conormal.chartCoborderHom i φ ψ f hf)
    (coborderGradeSheaf (Hom.Conormal.ι i φ)) W.unop
    (chartGradeToPushforwardCone i φ ψ f hf W.unop)

/-- Presheaf chart coborder associated-graded comparison. -/
def chartGradeToPushforwardPresheaf {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    coborderGradePresheaf (Hom.Conormal.ι i ψ) ⟶
      ((commRingPushforward (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).obj where
  app := chartGradeToPushforwardApp i φ ψ f hf
  naturality := fun _ _ _ ↦ sorry

/-- Pushforward chart coborder associated-graded comparison. -/
def chartGradeToPushforward {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    coborderGradeSheaf (Hom.Conormal.ι i ψ) ⟶
      (commRingPushforward (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ)) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i ψ)))
      (chartGradeToPushforwardPresheaf i φ ψ f hf)
      ((commRingPushforward (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i φ))).property⟩

/-- Inverse-image chart coborder associated-graded comparison. -/
def chartGradeRestrictSheaf {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (commRingInverseImage (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
      (coborderGradeSheaf (Hom.Conormal.ι i ψ)) ⟶
      coborderGradeSheaf (Hom.Conormal.ι i φ) :=

  ((commRingInverseImageAdjunction
    (Hom.Conormal.chartCoborderHom i φ ψ f hf)).homEquiv _ _).symm
      (chartGradeToPushforward i φ ψ f hf)

/-- The pulled coborder associated graded of `ι i ψ` maps to that of `ι i φ` after
scalar extension. -/
theorem chartGradeRestrict_w {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullbackSheafFunctor
          (Hom.Conormal.chartCoborderHom i φ ψ f hf)).map
        (coborderStructureMap (Hom.Conormal.ι i ψ)) ≫
      (pullbackSheafFunctorIso
          (Hom.Conormal.chartCoborderHom i φ ψ f hf)).hom.app
        (coborderGradeSheaf (Hom.Conormal.ι i ψ)) ≫
        chartGradeRestrictSheaf i φ ψ f hf =
      QcAlgebraUnder.inverseImageStructure (Hom.Conormal.chartCoborderHom i φ ψ f hf) ≫
        coborderStructureMap (Hom.Conormal.ι i φ) :=
  sorry

/-- Right-hand sheaf of the chart coborder associated-graded comparison. -/
def chartGradeRestrictRight {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    ((QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderTotal (Hom.Conormal.ι i ψ))).obj.right ⟶
      (coborderTotal (Hom.Conormal.ι i φ)).obj.right :=
  pushout.desc
    ((pullbackSheafFunctorIso
          (Hom.Conormal.chartCoborderHom i φ ψ f hf)).hom.app
        (coborderGradeSheaf (Hom.Conormal.ι i ψ)) ≫
      chartGradeRestrictSheaf i φ ψ f hf)
    (coborderStructureMap (Hom.Conormal.ι i φ))
    (chartGradeRestrict_w i φ ψ f hf)

/-- The chart coborder associated-graded comparison commutes with structure maps. -/
theorem chartGradeRestrictRight_w {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    ((QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderTotal (Hom.Conormal.ι i ψ))).obj.hom ≫
      chartGradeRestrictRight i φ ψ f hf =
      (coborderTotal (Hom.Conormal.ι i φ)).obj.hom :=
  sorry

/-- Comparison of coborder associated graded algebras along `chartCoborderHom`. -/
def chartGradeRestrict {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
      (coborderTotal (Hom.Conormal.ι i ψ)) ⟶
      coborderTotal (Hom.Conormal.ι i φ) :=
  homMk (Under.homMk (chartGradeRestrictRight i φ ψ f hf)
    (chartGradeRestrictRight_w i φ ψ f hf))

/-- The coborder kernel of `ι i φ` is contained in the coborder kernel of `ι i ψ` after
identifying sections along étale postcomposition. -/
theorem chartGrade_le_comap_inv {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i φ)) W ≤
      Ideal.comap (RingHom.id _)
        (KernelIdeal.sectionIdeal (coborderKernelMap (Hom.Conormal.ι i ψ))
          (op ((Modules.restrictPostcompose
              (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W.unop))) :=
  sorry

/-- Reverse associated-graded map on sections along `chartCoborderHom`. -/
def chartGradeRestrictInvToObj {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    coborderGradeObj (Hom.Conormal.ι i φ) W ⟶
      coborderGradeObj (Hom.Conormal.ι i ψ)
        (op ((Modules.restrictPostcompose
            (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W.unop)) :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map (RingHom.id _)
      (chartGrade_le_comap_inv i φ ψ f hf W))

/-- Component at `W` of the reverse chart coborder associated-graded comparison. -/
def chartGradeRestrictInvApp {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ)
    (W : (smallEtaleSite (Hom.coborder (Hom.Conormal.ι i φ)))ᵒᵖ) :
    coborderGradeObj (Hom.Conormal.ι i φ) W ⟶
      ((restrictSheaf (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i ψ))).obj.obj W :=
  chartGradeRestrictInvToObj i φ ψ f hf W ≫
    (toSheafify (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i ψ)))
        (coborderGradePresheaf (Hom.Conormal.ι i ψ))).app
      (op ((Modules.restrictPostcompose
          (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj W.unop))

/-- Presheaf reverse chart coborder associated-graded comparison. -/
def chartGradeRestrictInvPresheaf {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    coborderGradePresheaf (Hom.Conormal.ι i φ) ⟶
      ((restrictSheaf (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i ψ))).obj where
  app := chartGradeRestrictInvApp i φ ψ f hf
  naturality := fun _ _ _ ↦ sorry

/-- Sheaf reverse chart coborder associated-graded comparison. -/
def chartGradeRestrictInvSheaf {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    coborderGradeSheaf (Hom.Conormal.ι i φ) ⟶
      (restrictSheaf (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i ψ)) :=
  ⟨sheafifyLift (smallEtaleTopology (Hom.coborder (Hom.Conormal.ι i φ)))
      (chartGradeRestrictInvPresheaf i φ ψ f hf)
      ((restrictSheaf (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderGradeSheaf (Hom.Conormal.ι i ψ))).property⟩

/-- Reverse sheaf of the chart coborder associated-graded comparison. -/
def chartGradeRestrictInvRight {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (coborderTotal (Hom.Conormal.ι i φ)).obj.right ⟶
      ((QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderTotal (Hom.Conormal.ι i ψ))).obj.right :=
  chartGradeRestrictInvSheaf i φ ψ f hf ≫
    (restrictSheafIsoPullbackSheaf
        (Hom.Conormal.chartCoborderHom i φ ψ f hf)).hom.app
      (coborderGradeSheaf (Hom.Conormal.ι i ψ)) ≫
    pushout.inl
      ((QcAlgebraUnder.pullbackSheafFunctor
          (Hom.Conormal.chartCoborderHom i φ ψ f hf)).map
        (coborderStructureMap (Hom.Conormal.ι i ψ)))
      (QcAlgebraUnder.inverseImageStructure
        (Hom.Conormal.chartCoborderHom i φ ψ f hf))

/-- The reverse chart coborder associated-graded comparison commutes with structure maps. -/
theorem chartGradeRestrictInvRight_w {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (coborderTotal (Hom.Conormal.ι i φ)).obj.hom ≫
      chartGradeRestrictInvRight i φ ψ f hf =
      ((QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderTotal (Hom.Conormal.ι i ψ))).obj.hom :=
  sorry

/-- Reverse comparison of coborder associated graded algebras along `chartCoborderHom`. -/
def chartGradeRestrictInv {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    coborderTotal (Hom.Conormal.ι i φ) ⟶
      (QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
        (coborderTotal (Hom.Conormal.ι i ψ)) :=
  homMk (Under.homMk (chartGradeRestrictInvRight i φ ψ f hf)
    (chartGradeRestrictInvRight_w i φ ψ f hf))

/-- Identification of the pulled coborder associated graded of `ι i ψ` with that of
`ι i φ`. -/
def chartGradeRestrictIso {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.chartCoborderHom i φ ψ f hf)).obj
      (coborderTotal (Hom.Conormal.ι i ψ)) ≅
      coborderTotal (Hom.Conormal.ι i φ) where
  hom := chartGradeRestrict i φ ψ f hf
  inv := chartGradeRestrictInv i φ ψ f hf
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Transport of `C_{Z_V/V,*}` along `spaceMap`, using algebra `pullbackComp` and
`pullbackCongr` of `spaceMap ≫ liftCoborder (ι i ψ) = liftCoborder (ι i φ) ≫
chartCoborderHom`, together with the coborder associated-graded comparison of the
chart square. -/
def restrictEtaleιReassoc {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).obj
        (total (Hom.Conormal.ι i ψ)) ≅
      total (Hom.Conormal.ι i φ) :=
  (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).mapIso
      (totalIso (Hom.Conormal.ι i ψ)).symm ≪≫
    (pullbackComp (Hom.Conormal.spaceMap i φ ψ f hf)
        (IsImmersion.liftCoborder (Hom.Conormal.ι i ψ))).app
      (coborderTotal (Hom.Conormal.ι i ψ)) ≪≫
    (pullbackCongr (Hom.Conormal.chartLiftCoborder_comp i φ ψ f hf)).app
      (coborderTotal (Hom.Conormal.ι i ψ)) ≪≫
    (pullbackComp (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))
        (Hom.Conormal.chartCoborderHom i φ ψ f hf)).symm.app
      (coborderTotal (Hom.Conormal.ι i ψ)) ≪≫
    (QcAlgebraUnder.pullback
        (IsImmersion.liftCoborder (Hom.Conormal.ι i φ))).mapIso
      (chartGradeRestrictIso i φ ψ f hf) ≪≫
    totalIso (Hom.Conormal.ι i φ)

/-- The identification `C_{Z/X,*}|_{Z_U} ≅ C_{Z_U/U,*}` is functorial in morphisms of
étale charts: pullback of `restrictEtale i ψ` along `spaceMap` equals
`restrictEtale i φ` after the `toZ` and `ι` reassociations. -/
theorem restrictEtale_natural {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ]
    (f : ofOver U ⟶ ofOver V) (hf : f ≫ ψ = φ) :
    (QcAlgebraUnder.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).map
          (restrictEtale i ψ).hom ≫
        (restrictEtaleιReassoc i φ ψ f hf).hom =
      (restrictEtaleToZReassoc i φ ψ f hf).hom ≫ (restrictEtale i φ).hom :=
  sorry

/-- `Z_U ⟶ U` is a locally closed immersion, `Z_U` is a scheme, and `restrictEtale`
has the constructed comparison maps. -/
theorem restrictEtale_spec :
    (restrictEtale i φ).hom = restrictEtaleHom i φ ∧
      (restrictEtale i φ).inv = restrictEtaleInv i φ ∧
      IsImmersion (Hom.Conormal.ι i φ) ∧ IsScheme (Hom.Conormal.space i φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
