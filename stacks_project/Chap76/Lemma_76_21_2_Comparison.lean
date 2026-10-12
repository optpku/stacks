/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_26_1_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent
public import stacks_project.Chap76.Lemma_76_25_1_Pullback

/-!
# Étale restriction of naive cotangent complexes of algebraic spaces

A commutative square of algebraic spaces over a scheme `S` with étale vertical arrows
identifies the restriction of `NL_f` along `p` with `NL_g` as complexes of `𝒪_U`-modules,
hence in `D(𝒪_U)`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MorphismProperty
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open Algebra Algebra.Extension Algebra.Generators
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalCommRing
open ComplexShape
open scoped AlgebraicGeometry.AlgebraicSpace ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

variable {S : Scheme.{u}}

/-- The object of `X_étale` obtained by postcomposing an étale chart of `U` with `p`. -/
abbrev restrictChart {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) : (smallEtaleSite X)ᵒᵖ :=
  op ((restrictPostcompose p).obj W.unop)

/-- Restriction of `𝒪_X` along the étale site functor of `p`, as a commutative-ring map. -/
def structureCoeff {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) :
    (commStructureSheaf X).obj.obj (restrictChart p W) ⟶
      (commStructureSheaf U).obj.obj W :=
  CommRingCat.ofHom
    { toFun := (restrictStructureMap p).hom.app W
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Inverse of `structureCoeff`, identity on sections. -/
def structureCoeffInv {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) :
    (commStructureSheaf U).obj.obj W ⟶
      (commStructureSheaf X).obj.obj (restrictChart p W) :=
  CommRingCat.ofHom
    { toFun := (restrictStructureMapInv p).hom.app W
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

/-- Inverse image of types along a composite morphism of algebraic spaces. -/
def inverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    (morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage ≅
      (morphismOfTopoi (p ≫ f)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
    (morphismOfTopoi (p ≫ f)).adjunction (typePushforwardComp p f)

/-- Lift a type-valued map of forgotten ring sheaves to a morphism of ring sheaves. -/
def ringSheafHomOfTypeHom {Z : AlgebraicSpace S}
    {R T : Sheaf (smallEtaleTopology Z) RingCat.{u}}
    (φ : (sheafCompose (smallEtaleTopology Z) (forget RingCat.{u})).obj R ⟶
      (sheafCompose (smallEtaleTopology Z) (forget RingCat.{u})).obj T) :
    R ⟶ T :=
  ⟨{ app := fun U ↦
        RingCat.ofHom
          { toFun := ((sheafToPresheaf (smallEtaleTopology Z) (Type u)).map φ).app U
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
     naturality := fun _ _ _ ↦ sorry }⟩

/-- Lift a type-valued isomorphism of forgotten ring sheaves to an isomorphism of ring sheaves. -/
def ringSheafIsoOfTypeIso {Z : AlgebraicSpace S}
    {R T : Sheaf (smallEtaleTopology Z) RingCat.{u}}
    (e : (sheafCompose (smallEtaleTopology Z) (forget RingCat.{u})).obj R ≅
      (sheafCompose (smallEtaleTopology Z) (forget RingCat.{u})).obj T) :
    R ≅ T where
  hom := ringSheafHomOfTypeHom e.hom
  inv := ringSheafHomOfTypeHom e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Successive ring-valued inverse images identify with inverse image along the composite. -/
def ringInverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) RingCat.{u}) :
    (morphismOfTopoi p).ringInverseImage.obj ((morphismOfTopoi f).ringInverseImage.obj R) ≅
      (morphismOfTopoi (p ≫ f)).ringInverseImage.obj R :=
  ringSheafIsoOfTypeIso
    ((morphismOfTopoi p).ringInverseImageForgetIso.app
        ((morphismOfTopoi f).ringInverseImage.obj R) ≪≫
      (morphismOfTopoi p).inverseImage.mapIso
        ((morphismOfTopoi f).ringInverseImageForgetIso.app R) ≪≫
      (inverseImageCompIso p f).app
        ((sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj R) ≪≫
      ((morphismOfTopoi (p ≫ f)).ringInverseImageForgetIso.app R).symm)

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def pullbackSheafFunctorComp {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    QcAlgebraUnder.pullbackSheafFunctor f ⋙ QcAlgebraUnder.pullbackSheafFunctor p ≅
      QcAlgebraUnder.pullbackSheafFunctor (p ≫ f) :=
  NatIso.ofComponents
    (fun A ↦
      (CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}
          (J := smallEtaleTopology U)).preimageIso
        (ringInverseImageCompIso p f
          ((sheafCompose (smallEtaleTopology Y)
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A)))
    sorry

/-- Restriction of commutative-ring sheaves along an étale morphism, by postcomposition
on small étale sites. -/
def restrictSheaf {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology U) CommRingCat.{u} :=
  (restrictPostcompose p).sheafPushforwardContinuous CommRingCat.{u}
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- Identity-on-sections comparison `(p_small⁻¹ 𝒪_X) ⟶ 𝒪_U` of commutative-ring sheaves. -/
def restrictCommStructureMap {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictSheaf p).obj (commStructureSheaf X) ⟶ commStructureSheaf U :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := fun _ _ _ ↦ sorry }⟩

/-- Identity-on-sections inverse `𝒪_U ⟶ (p_small⁻¹ 𝒪_X)` of commutative-ring sheaves. -/
def restrictCommStructureMapInv {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    commStructureSheaf U ⟶ (restrictSheaf p).obj (commStructureSheaf X) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := fun _ _ _ ↦ sorry }⟩

/-- The identification `p_small⁻¹ 𝒪_X ≅ 𝒪_U` of commutative-ring sheaves, given by identity
on sections. -/
def restrictCommStructureIso {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictSheaf p).obj (commStructureSheaf X) ≅ commStructureSheaf U where
  hom := restrictCommStructureMap p
  inv := restrictCommStructureMapInv p
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The opposite of étale restriction has pointwise right Kan extensions on type-valued
presheaves. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension_type
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (P : (smallEtaleSite U)ᵒᵖ ⥤ Type u) :
    (etaleRestriction p).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The opposite of spaces étale restriction has pointwise right Kan extensions on type-valued
presheaves. -/
instance spacesEtaleRestriction_op_hasPointwiseRightKanExtension_type
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (P : (spacesEtaleSite U)ᵒᵖ ⥤ Type u) :
    (spacesEtaleRestriction p).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Spaces étale restriction is cocontinuous, as the left adjoint of continuous pullback. -/
instance spacesEtaleRestriction_isCocontinuous {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (spacesEtaleRestriction p).IsCocontinuous (spacesEtaleTopology U) (spacesEtaleTopology X) :=
  Functor.ContinuousRightAdjoint.left_isCocontinuous
    (spacesEtaleRestriction p) (spacesEtalePullback p)
    (MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ p inferInstance trivial)

/-- Small étale inclusion followed by spaces étale restriction is cocontinuous. -/
instance smallEtaleInclusion_comp_spacesEtaleRestriction_isCocontinuous
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (smallEtaleInclusion U ⋙ spacesEtaleRestriction p).IsCocontinuous
      (smallEtaleTopology U) (spacesEtaleTopology X) :=
  isCocontinuous_comp (smallEtaleInclusion U) (spacesEtaleRestriction p)
    (smallEtaleTopology U) (spacesEtaleTopology U)

/-- Étale restriction followed by the spaces inclusion is cocontinuous. -/
instance etaleRestriction_comp_smallEtaleInclusion_isCocontinuous
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (etaleRestriction p ⋙ smallEtaleInclusion X).IsCocontinuous
      (smallEtaleTopology U) (spacesEtaleTopology X) :=
  isCocontinuous_comp (etaleRestriction p) (smallEtaleInclusion X)
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- The opposite of the composite of small étale inclusion with spaces étale restriction has
pointwise right Kan extensions on type-valued presheaves. -/
instance inclusionRestriction_hasPointwiseRan
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (P : (smallEtaleSite U)ᵒᵖ ⥤ Type u) :
    (smallEtaleInclusion U ⋙ spacesEtaleRestriction p).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The opposite of the composite of étale restriction with the spaces inclusion has pointwise
right Kan extensions on type-valued presheaves. -/
instance restrictionInclusion_hasPointwiseRan
    {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (P : (smallEtaleSite U)ᵒᵖ ⥤ Type u) :
    (etaleRestriction p ⋙ smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

/-- `smallEtaleInclusion` is full, as the comma comparison along `ofOverFunctor`. -/
instance smallEtaleInclusion_full (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).Full :=
  inferInstanceAs
    ((MorphismProperty.CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) Y).Full)

/-- `smallEtaleInclusion` is faithful, as the comma comparison along `ofOverFunctor`. -/
instance smallEtaleInclusion_faithful (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).Faithful :=
  inferInstanceAs
    ((MorphismProperty.CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) Y).Faithful)

/-- The opposite of `smallEtaleInclusion` is full. -/
instance smallEtaleInclusion_op_full (Y : AlgebraicSpace S) :
    ((smallEtaleInclusion Y).op).Full :=
  inferInstance

/-- The opposite of `smallEtaleInclusion` is faithful. -/
instance smallEtaleInclusion_op_faithful (Y : AlgebraicSpace S) :
    ((smallEtaleInclusion Y).op).Faithful :=
  inferInstance

/-- The opposite of `smallEtaleInclusion` has pointwise right Kan extensions on type-valued
presheaves. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension_type
    (Y : AlgebraicSpace S) (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (smallEtaleInclusion Y).op.HasPointwiseRightKanExtension P :=
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
  isoWhiskerRight
    (Adjunction.rightAdjointUniq (EtaleTopos.siteEquivalence Y).toAdjunction
      ((smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y))).symm
    ((smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)) ≪≫
    EtaleTopos.extensionRestrictionIso Y

/-- Direct image of type-valued sheaves along an étale morphism agrees with cocontinuous
pushforward of `etaleRestriction`. -/
def typePushforwardIsoEtaleCocontinuous {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    typePushforward p ≅
      (etaleRestriction p).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) :=
  let iU :=
    (smallEtaleInclusion U).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology U) (spacesEtaleTopology U)
  let iXrestrict :=
    (smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let rSpaces :=
    (spacesEtaleRestriction p).sheafPushforwardCocontinuous (Type u)
      (spacesEtaleTopology U) (spacesEtaleTopology X)
  let iXextend :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let jCocont :=
    (etaleRestriction p).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X)
  typePushforwardFactor p ≪≫
    isoWhiskerRight
      (Adjunction.rightAdjointUniq (EtaleTopos.siteEquivalence U).toAdjunction
        ((smallEtaleInclusion U).sheafAdjunctionCocontinuous (Type u)
          (smallEtaleTopology U) (spacesEtaleTopology U)))
      ((spacesEtalePullback p).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology X) (spacesEtaleTopology U) ⋙ iXrestrict) ≪≫
    isoWhiskerLeft iU (isoWhiskerRight
      (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
        (spacesEtaleRestriction p) (spacesEtalePullback p) (Type u)
        (MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ p inferInstance trivial))
      iXrestrict) ≪≫
    (Functor.associator iU rSpaces iXrestrict).symm ≪≫
    isoWhiskerRight
      (sheafPushforwardCocontinuousComp' (smallEtaleTopology U) (spacesEtaleTopology U)
          (spacesEtaleTopology X) (smallEtaleInclusion U) (spacesEtaleRestriction p)
          (etaleRestriction_comp_inclusion p).symm)
      iXrestrict ≪≫
    isoWhiskerRight
      (sheafPushforwardCocontinuousComp (smallEtaleTopology U) (smallEtaleTopology X)
          (spacesEtaleTopology X) (etaleRestriction p) (smallEtaleInclusion X)).symm
      iXrestrict ≪≫
    Functor.associator jCocont iXextend iXrestrict ≪≫
    isoWhiskerLeft jCocont (smallEtaleInclusionCocontinuousContinuousIso X) ≪≫
    Functor.rightUnitor jCocont

/-- Étale restriction of type-valued sheaves along `restrictPostcompose` identifies with
inverse image of the associated morphism of small étale topoi. -/
def restrictTypeIsoInverseImage {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X) ≅
      (morphismOfTopoi p).inverseImage :=
  Functor.sheafPushforwardContinuousIso (restrictPostcomposeIso p) (Type u)
      (smallEtaleTopology U) (smallEtaleTopology X) ≪≫
    Adjunction.leftAdjointUniq
      ((etaleRestriction p).sheafAdjunctionCocontinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X))
      ((morphismOfTopoi p).adjunction.ofNatIsoRight (typePushforwardIsoEtaleCocontinuous p))

/-- Forgotten étale restriction of commutative-ring sheaves agrees with ring inverse image. -/
def restrictSheafForgetRingIso {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((restrictSheaf p).obj A) ≅
      (sheafCompose (smallEtaleTopology U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((QcAlgebraUnder.pullbackSheafFunctor p).obj A) :=
  ringSheafIsoOfTypeIso
    ((sheafCompose (smallEtaleTopology U) (forget RingCat.{u})).mapIso
        (eqToIso (congrArg (fun G ↦ G.obj A)
          (Functor.sheafPushforwardContinuous.compSheafCompose
            (restrictPostcompose p) (forget₂ CommRingCat.{u} RingCat.{u})
            (smallEtaleTopology U) (smallEtaleTopology X)))) ≪≫
      eqToIso (congrArg (fun G ↦ G.obj
          ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
        (Functor.sheafPushforwardContinuous.compSheafCompose
          (restrictPostcompose p) (forget RingCat.{u})
          (smallEtaleTopology U) (smallEtaleTopology X))) ≪≫
      (restrictTypeIsoInverseImage p).app
        ((sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj
          ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) ≪≫
      ((morphismOfTopoi p).ringInverseImageForgetIso.app
          ((sheafCompose (smallEtaleTopology X)
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A)).symm) ≪≫
    (QcAlgebraUnder.pullbackSheafFunctor_forgetRingIso p A).symm

/-- Étale restriction of commutative-ring sheaves is isomorphic to inverse image in the
algebra-pullback presentation. -/
def restrictSheafIsoPullbackSheaf {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    restrictSheaf p ≅ QcAlgebraUnder.pullbackSheafFunctor p :=
  NatIso.ofComponents
    (fun A ↦
      (CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}
          (J := smallEtaleTopology U)).preimageIso
        (restrictSheafForgetRingIso p A))
    sorry

/-- The inverse-image form `f⁻¹𝒪_Y` is algebra-pullback of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_eq_pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f =
      (QcAlgebraUnder.pullbackSheafFunctor f).obj (commStructureSheaf Y) :=
  rfl

/-- For an étale morphism, the inverse-image form `f⁻¹𝒪_Y` identifies with `𝒪_X`. -/
def commInverseImageStructureSheafIso_of_etale {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    commInverseImageStructureSheaf f ≅ commStructureSheaf X :=
  eqToIso (commInverseImageStructureSheaf_eq_pullback f) ≪≫
    (restrictSheafIsoPullbackSheaf f).symm.app (commStructureSheaf Y) ≪≫
    restrictCommStructureIso f


/-- Evaluation of étale restriction of a commutative-ring sheaf recovers the original
sections on the postcomposed chart. -/
theorem restrictSheaf_obj_obj {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) (W : (smallEtaleSite U)ᵒᵖ) :
    ((restrictSheaf p).obj A).obj.obj W = A.obj.obj (restrictChart p W) :=
  rfl

/-- The comparison `p⁻¹ f⁻¹ 𝒪_Y ≅ g⁻¹ 𝒪_V` of coefficient sheaves of a commutative étale
square, as étale restriction of `f⁻¹𝒪_Y`. -/
def inverseImageCoeffSheafIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictSheaf p).obj (commInverseImageStructureSheaf f) ≅
      commInverseImageStructureSheaf g :=
  (restrictSheafIsoPullbackSheaf p).app (commInverseImageStructureSheaf f) ≪≫
    eqToIso (congrArg (QcAlgebraUnder.pullbackSheafFunctor p).obj
      (commInverseImageStructureSheaf_eq_pullback f)) ≪≫
    (pullbackSheafFunctorComp p f).app (commStructureSheaf Y) ≪≫
    eqToIso (congrArg
      (fun h : U ⟶ Y ↦ (QcAlgebraUnder.pullbackSheafFunctor h).obj (commStructureSheaf Y))
      hcomm) ≪≫
    (pullbackSheafFunctorComp g q).symm.app (commStructureSheaf Y) ≪≫
    eqToIso (congrArg (QcAlgebraUnder.pullbackSheafFunctor g).obj
      (commInverseImageStructureSheaf_eq_pullback q).symm) ≪≫
    (QcAlgebraUnder.pullbackSheafFunctor g).mapIso
      (commInverseImageStructureSheafIso_of_etale q) ≪≫
    eqToIso (commInverseImageStructureSheaf_eq_pullback g).symm

/-- The comparison `p⁻¹ f⁻¹ 𝒪_Y ⟶ g⁻¹ 𝒪_V` of coefficient sheaves of a commutative étale
square, as étale restriction of `f⁻¹𝒪_Y`. -/
def inverseImageCoeffSheaf {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictSheaf p).obj (commInverseImageStructureSheaf f) ⟶
      commInverseImageStructureSheaf g :=
  (inverseImageCoeffSheafIso p g f q hcomm).hom

/-- The objectwise coefficient map `f⁻¹𝒪_Y(jW) ⟶ g⁻¹𝒪_V(W)` of a commutative étale square. -/
def inverseImageCoeff {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    (commInverseImageStructureSheaf f).obj.obj (restrictChart p W) ⟶
      (commInverseImageStructureSheaf g).obj.obj W :=
  eqToHom (restrictSheaf_obj_obj p (commInverseImageStructureSheaf f) W).symm ≫
    (inverseImageCoeffSheaf p g f q hcomm).hom.app W

/-- The reverse objectwise coefficient map `g⁻¹𝒪_V(W) ⟶ f⁻¹𝒪_Y(jW)` of a commutative étale
square. -/
def inverseImageCoeffInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    (commInverseImageStructureSheaf g).obj.obj W ⟶
      (commInverseImageStructureSheaf f).obj.obj (restrictChart p W) :=
  (inverseImageCoeffSheafIso p g f q hcomm).inv.hom.app W ≫
    eqToHom (restrictSheaf_obj_obj p (commInverseImageStructureSheaf f) W)

/-- The polynomial-ring map of canonical presentations induced by a commutative étale square. -/
def squarePresentationRingHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) →+*
      MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) :=
  (MvPolynomial.map (inverseImageCoeff p g f q hcomm W).hom).comp
    (MvPolynomial.rename fun s ↦ (structureCoeff p W).hom s).toRingHom

/-- The algebra homomorphism of canonical presentations induced by a commutative étale square. -/
def squarePresentationAlgHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra
  ({ squarePresentationRingHom p g f q hcomm W with
      commutes' := fun _ ↦ sorry } :
    MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) →ₐ[
      (commInverseImageStructureSheaf f).obj.obj (restrictChart p W)]
      MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W))

/-- The kernel of the canonical presentation is compatible with the square comparison. -/
theorem squarePresentationKer_le_comap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
    letI := inverseImageAlgebra g W
    (presentation f (restrictChart p W)).ker ≤
      (presentation g W).ker.comap
        (squarePresentationRingHom p g f q hcomm W) :=
  sorry

/-- Scalar tower of the named maps `inverseImageCoeff`, `commInverseImageStructureSheafMap g`,
and their composite, through `g⁻¹𝒪_V(W)`. -/
theorem square_isScalarTower_inverseImage {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use the scalar action from this square's inverse-image coefficient map at W.
    letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
    -- Local instance justification (defeq pin): use g's inverse-image algebra at the fixed chart W in the tensor product.
    letI := inverseImageAlgebra g W
    -- Local instance justification (defeq pin): the composite scalar action below is the one specified by the preceding two coefficient maps.
    letI : Algebra
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
        ((commStructureSheaf U).obj.obj W) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
          (inverseImageCoeff p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf U).obj.obj W) :=
  sorry

/-- Scalar tower of the named maps `commInverseImageStructureSheafMap f`, `structureCoeff`,
and the composite `commInverseImageStructureSheafMap g` after `inverseImageCoeff`. -/
theorem square_isScalarTower_structure {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use f's inverse-image algebra on the restricted chart for this scalar-extension map.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (defeq pin): the target scalar action is induced by the chart's structure-coefficient homomorphism.
    letI := RingHom.toAlgebra (structureCoeff p W).hom
    -- Local instance justification (defeq pin): use the composite of these two chartwise scalar actions in the tensor construction below.
    letI : Algebra
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
        ((commStructureSheaf U).obj.obj W) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
          (inverseImageCoeff p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf X).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
  sorry

/-- The morphism of canonical presentations induced by a commutative étale square. -/
def squarePresentationHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W
  ({ toRingHom := squarePresentationRingHom p g f q hcomm W
     toRingHom_algebraMap := fun _ ↦ sorry
     algebraMap_toRingHom := fun _ ↦ sorry } :
    ((presentation f (restrictChart p W)).toExtension).Hom
      ((presentation g W).toExtension))

/-- Objectwise comparison of conormal terms of a commutative étale square. -/
def cotangentObj_squareMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentObj f (restrictChart p W) ⟶
      (ModuleCat.restrictScalars (structureCoeff p W).hom).obj (cotangentObj g W) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj (restrictChart p W)))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation f (restrictChart p W)).ker
            (presentation g W).ker
            (squarePresentationAlgHom p g f q hcomm W) sorry
            (Cotangent.val (P := (presentation f (restrictChart p W)).toExtension) x))
      map_add' := sorry
      map_smul' := sorry }

/-- Objectwise comparison of presentation cotangent-space terms of a commutative étale square. -/
def cotangentSpaceObj_squareMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentSpaceObj f (restrictChart p W) ⟶
      (ModuleCat.restrictScalars (structureCoeff p W).hom).obj
        (cotangentSpaceObj g W) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj (restrictChart p W)))
    (CotangentSpace.map (squarePresentationHom p g f q hcomm W))

/-- Presheaf-level comparison of conormal terms after étale restriction of sites. -/
def cotangentPresheaf_squareHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f) ⟶
      cotangentPresheaf g where
  app := cotangentObj_squareMap p g f q hcomm
  naturality := sorry

/-- Presheaf-level comparison of presentation cotangent-space terms after étale restriction. -/
def cotangentSpacePresheaf_squareHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj
        (cotangentSpacePresheaf f) ⟶
      cotangentSpacePresheaf g where
  app := cotangentSpaceObj_squareMap p g f q hcomm
  naturality := sorry

/-- The reverse polynomial-ring map of canonical presentations of a commutative étale square. -/
def squarePresentationRingHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) →+*
      MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) :=
  (MvPolynomial.rename fun s ↦ (structureCoeffInv p W).hom s).toRingHom.comp
    (MvPolynomial.map (inverseImageCoeffInv p g f q hcomm W).hom)

/-- The reverse algebra homomorphism of canonical presentations of a commutative étale square. -/
def squarePresentationAlgHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra
  ({ squarePresentationRingHomInv p g f q hcomm W with
      commutes' := fun _ ↦ sorry } :
    MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) →ₐ[
      (commInverseImageStructureSheaf g).obj.obj W]
      MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)))

/-- Reverse scalar tower of the named maps `inverseImageCoeffInv`,
`commInverseImageStructureSheafMap f`, and their composite. -/
theorem square_isScalarTower_inverseImage_inv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use the inverse coefficient homomorphism's scalar action for this inverse comparison.
    letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
    -- Local instance justification (defeq pin): use f's inverse-image algebra at the restricted chart in the inverse tensor map.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (defeq pin): compose these fixed chartwise actions to match the source algebra of the inverse map.
    letI : Algebra
        ((commInverseImageStructureSheaf g).obj.obj W)
        ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
          (inverseImageCoeffInv p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
  sorry

/-- The reverse kernel comparison of canonical presentations of a commutative étale square. -/
theorem squarePresentationKer_le_comap_inv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
    letI := inverseImageAlgebra g W
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
    letI := inverseImageAlgebra f (restrictChart p W)
    (presentation g W).ker ≤
      (presentation f (restrictChart p W)).ker.comap
        (squarePresentationRingHomInv p g f q hcomm W) :=
  sorry

/-- Reverse objectwise comparison of conormal terms of a commutative étale square. -/
def cotangentObj_squareMapInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentObj g W ⟶
      (ModuleCat.restrictScalars (structureCoeffInv p W).hom).obj
        (cotangentObj f (restrictChart p W)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf U).obj.obj W))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation g W).ker
            (presentation f (restrictChart p W)).ker
            (squarePresentationAlgHomInv p g f q hcomm W) sorry
            (Cotangent.val (P := (presentation g W).toExtension) x))
      map_add' := sorry
      map_smul' := sorry }

/-- The reverse morphism of canonical presentations of a commutative étale square. -/
def squarePresentationHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W
  ({ toRingHom := squarePresentationRingHomInv p g f q hcomm W
     toRingHom_algebraMap := fun _ ↦ sorry
     algebraMap_toRingHom := fun _ ↦ sorry } :
    ((presentation g W).toExtension).Hom
      ((presentation f (restrictChart p W)).toExtension))

/-- Reverse objectwise comparison of presentation cotangent-space terms. -/
def cotangentSpaceObj_squareMapInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentSpaceObj g W ⟶
      (ModuleCat.restrictScalars (structureCoeffInv p W).hom).obj
        (cotangentSpaceObj f (restrictChart p W)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf U).obj.obj W))
    (CotangentSpace.map (squarePresentationHomInv p g f q hcomm W))

/-- Reverse presheaf-level comparison of conormal terms after étale restriction of sites. -/
def cotangentPresheaf_squareHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentPresheaf g ⟶
      (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f) where
  app := cotangentObj_squareMapInv p g f q hcomm
  naturality := sorry

/-- Reverse presheaf-level comparison of presentation cotangent-space terms. -/
def cotangentSpacePresheaf_squareHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSpacePresheaf g ⟶
      (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj
        (cotangentSpacePresheaf f) where
  app := cotangentSpaceObj_squareMapInv p g f q hcomm
  naturality := sorry

/-- Sheafification unit of an `𝒪_Y`-module presheaf, pushed forward along étale restriction. -/
def restrictSheafificationUnit {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P ⟶
      (SheafOfModules.forget _).obj
        ((restrictFunctor h).obj
          ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P)) :=
  (PresheafOfModules.pushforward (restrictStructureMap h).hom).map
    ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf X).obj)).unit.app P)

/-- Compatibility `sheafify(P|_{U_étale}) ⟶ (sheafify P)|_{U_étale}` as the unit/counit
composite `sheafify.map unit ≫ counit`. -/
def restrictSheafificationHom {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
        ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) ⟶
      (restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (restrictSheafificationUnit h P) ≫
    (PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf U).obj)).counit.app
      ((restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P))

/-- Étale restriction commutes with sheafification of module presheaves. -/
instance restrictSheafificationHom_isIso {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    IsIso (restrictSheafificationHom h P) :=
  sorry

/-- Inverse compatibility `(sheafify P)|_{U_étale} ⟶ sheafify(P|_{U_étale})`,
the inverse of `restrictSheafificationHom`. -/
def restrictSheafificationInv {U X : AlgebraicSpace S} (h : U ⟶ X) [Etale h]
    (P : PresheafOfModules.{u}
      ((commStructureSheaf X).obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    (restrictFunctor h).obj
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj P) ⟶
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).obj
        ((PresheafOfModules.pushforward (restrictStructureMap h).hom).obj P) :=
  CategoryTheory.inv (restrictSheafificationHom h P)

/-- Degree `-1` component of étale restriction of naive cotangent complexes. -/
def etaleRestrictHom_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictFunctor p).obj (cotangentSheaf f) ⟶ cotangentSheaf g :=
  restrictSheafificationInv p (cotangentPresheaf f) ≫
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentPresheaf_squareHom p g f q hcomm)

/-- Degree `0` component of étale restriction of naive cotangent complexes. -/
def etaleRestrictHom_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictFunctor p).obj (cotangentSpaceSheaf f) ⟶ cotangentSpaceSheaf g :=
  restrictSheafificationInv p (cotangentSpacePresheaf f) ≫
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentSpacePresheaf_squareHom p g f q hcomm)

/-- Degreewise components of the étale-restriction comparison of naive cotangent complexes. -/
def etaleRestrictHom_app {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (n : ℤ) :
    (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).X n ⟶
      (naiveCotangent g).X n :=
  match n with
  | Int.negSucc 0 => etaleRestrictHom_negOne p g f q hcomm
  | Int.ofNat 0 => etaleRestrictHom_zero p g f q hcomm
  | _ => 0

/-- The degreewise comparison maps commute with differentials. -/
theorem etaleRestrictHom_app_comm {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    etaleRestrictHom_app p g f q hcomm i ≫ (naiveCotangent g).d i j =
      (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).d i j ≫
        etaleRestrictHom_app p g f q hcomm j :=
  sorry

/-- The canonical comparison `((NL_f)|_{U_étale}) ⟶ NL_g` of complexes of `𝒪_U`-modules. -/
def etaleRestrictHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) ⟶
      naiveCotangent g where
  f n := etaleRestrictHom_app p g f q hcomm n
  comm' i j hij := etaleRestrictHom_app_comm p g f q hcomm i j hij

/-- The degree `-1` component of `etaleRestrictHom` is the conormal comparison. -/
theorem etaleRestrictHom_f_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictHom p g f q hcomm).f (-1) =
      etaleRestrictHom_negOne p g f q hcomm :=
  sorry

/-- The degree `0` component of `etaleRestrictHom` is the presentation-differentials comparison. -/
theorem etaleRestrictHom_f_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictHom p g f q hcomm).f 0 =
      etaleRestrictHom_zero p g f q hcomm :=
  sorry

/-- Degree `-1` component of the reverse étale restriction of naive cotangent complexes. -/
def etaleRestrictHomInv_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSheaf g ⟶ (restrictFunctor p).obj (cotangentSheaf f) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentPresheaf_squareHomInv p g f q hcomm) ≫
    restrictSheafificationHom p (cotangentPresheaf f)

/-- Degree `0` component of the reverse étale restriction of naive cotangent complexes. -/
def etaleRestrictHomInv_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSpaceSheaf g ⟶ (restrictFunctor p).obj (cotangentSpaceSheaf f) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentSpacePresheaf_squareHomInv p g f q hcomm) ≫
    restrictSheafificationHom p (cotangentSpacePresheaf f)

/-- Degreewise components of the reverse étale-restriction comparison. -/
def etaleRestrictHomInv_app {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (n : ℤ) :
    (naiveCotangent g).X n ⟶
      (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).X n :=
  match n with
  | Int.negSucc 0 => etaleRestrictHomInv_negOne p g f q hcomm
  | Int.ofNat 0 => etaleRestrictHomInv_zero p g f q hcomm
  | _ => 0

/-- The reverse degreewise comparison maps commute with differentials. -/
theorem etaleRestrictHomInv_app_comm {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    etaleRestrictHomInv_app p g f q hcomm i ≫
        (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).d i j =
      (naiveCotangent g).d i j ≫ etaleRestrictHomInv_app p g f q hcomm j :=
  sorry

/-- The reverse comparison `NL_g ⟶ ((NL_f)|_{U_étale})` of complexes of `𝒪_U`-modules. -/
def etaleRestrictHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    naiveCotangent g ⟶
      ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) where
  f n := etaleRestrictHomInv_app p g f q hcomm n
  comm' i j hij := etaleRestrictHomInv_app_comm p g f q hcomm i j hij

/-- The reverse comparison of étale restriction of naive cotangent complexes is an isomorphism. -/
instance etaleRestrictHomInv_isIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRestrictHomInv p g f q hcomm) :=
  sorry

/-- Étale restriction of naive cotangent complexes is an isomorphism of complexes. -/
instance etaleRestrictHom_isIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRestrictHom p g f q hcomm) :=
  sorry

/-- The canonical isomorphism `(NL_f)|_{U_étale} ≅ NL_g` of complexes of `𝒪_U`-modules. -/
def etaleRestrictIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) ≅
      naiveCotangent g where
  hom := etaleRestrictHom p g f q hcomm
  inv := etaleRestrictHomInv p g f q hcomm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The derived identification `NL_{X/Y}|_{U_étale} ≅ NL_{U/V}` in `D(𝒪_U)`. -/
def etaleRestrictIso_derived {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    DerivedCategory.Q.obj
        (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)) ≅
      DerivedCategory.Q.obj (naiveCotangent g) :=
  DerivedCategory.Q.mapIso (etaleRestrictIso p g f q hcomm)

/-- The derived identification is the image of `etaleRestrictIso` under `DerivedCategory.Q`. -/
theorem etaleRestrictIso_derived_hom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictIso_derived p g f q hcomm).hom =
      DerivedCategory.Q.map (etaleRestrictHom p g f q hcomm) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
