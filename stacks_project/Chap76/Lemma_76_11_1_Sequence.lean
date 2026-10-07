module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.SquareZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap76.Lemma_76_11_1_Presentation
public import stacks_project.Chap76.Lemma_76_9_6_Equivalence
public import stacks_project.Chap99.Situation_99_11_1_Pullback

/-!
# Picard cohomology sequence of a first-order thickening of algebraic spaces

The units short exact sequence of the inverse-image presentation of a
first-order thickening yields a canonical eight-term exact sequence of abelian
groups, with Picard groups of the algebraic spaces in the displayed degree-one
positions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The module category of an algebraic space is braided, so its Picard group
is commutative. The braiding is the transport of the canonical symmetry on
modules over the commutative presentation of `𝒪_Y`. -/
noncomputable instance instBraidedCategory {S : Scheme.{u}} (Y : AlgebraicSpace S) :
    BraidedCategory Y.Modules where
  braiding M N :=
    (commModulesEquivalence Y).functor.mapIso
      (β_ ((commModulesEquivalence Y).inverse.obj M)
        ((commModulesEquivalence Y).inverse.obj N))
  braiding_naturality_right := sorry
  braiding_naturality_left := sorry
  hexagon_forward := sorry
  hexagon_reverse := sorry

/-- Invertibility of an `𝒪_Y`-module transports to its universe lift. -/
instance liftModule_isInvertibleObject {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (L : Y.Modules) [isInvertibleObject L] :
    isInvertibleObject (liftModule L) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsFirstOrderThickening i]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
variable [hExt : HasExt.{u + 2}
  (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [hExt' : HasExt.{u + 2}
  (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]

/-- A first-order thickening is representable by schemes, so Lemma 76.9.6
applies. -/
theorem presentationRepresentable : yoneda.relativelyRepresentable i := sorry

/-- Base change along a first-order thickening, as a functor of small étale
sites. -/
abbrev presentationEtalePullback : smallEtaleSite X' ⥤ smallEtaleSite X :=
  smallEtalePullback i (presentationRepresentable i)

/-- `presentationEtalePullback i` is the small étale pullback of `i`. -/
theorem presentationEtalePullback_eq :
    presentationEtalePullback i =
      smallEtalePullback i (presentationRepresentable i) :=
  rfl

/-- Base change along a first-order thickening is continuous for the small étale
topologies. -/
instance presentationEtalePullback_isContinuous :
    (presentationEtalePullback i).IsContinuous
      (smallEtaleTopology X') (smallEtaleTopology X) := sorry

/-- Lemma 76.9.6: base change along a first-order thickening is an equivalence of
small étale sites. -/
instance presentationEtalePullback_isEquivalence :
    (presentationEtalePullback i).IsEquivalence :=
  smallEtalePullback.isEquivalence_of_isThickening i (presentationRepresentable i)

/-- The inverse of Lemma 76.9.6, as a functor of small étale sites. -/
abbrev presentationEtalePullbackInverse : smallEtaleSite X ⥤ smallEtaleSite X' :=
  (presentationEtalePullback i).asEquivalence.inverse

/-- `presentationEtalePullbackInverse i` is the inverse of
`presentationEtalePullback i`. -/
theorem presentationEtalePullbackInverse_eq :
    presentationEtalePullbackInverse i =
      (presentationEtalePullback i).asEquivalence.inverse :=
  rfl

/-- The inverse of Lemma 76.9.6 is continuous for the small étale topologies. -/
instance presentationEtalePullbackInverse_isContinuous :
    (presentationEtalePullbackInverse i).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology X') := sorry

/-- Continuity of the inverse in `asEquivalence.symm` form, used by
`Adjunction.sheafPushforwardContinuous`. -/
instance presentationEtalePullback_symm_functor_isContinuous :
    (presentationEtalePullback i).asEquivalence.symm.functor.IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology X') :=
  presentationEtalePullbackInverse_isContinuous i

/-- Continuity of the original functor in `asEquivalence.symm` form. -/
instance presentationEtalePullback_symm_inverse_isContinuous :
    (presentationEtalePullback i).asEquivalence.symm.inverse.IsContinuous
      (smallEtaleTopology X') (smallEtaleTopology X) :=
  presentationEtalePullback_isContinuous i

/-- The inverse of Lemma 76.9.6 is a dense subsite functor. -/
instance presentationEtalePullbackInverse_isDenseSubsite :
    (presentationEtalePullback i).asEquivalence.inverse.IsDenseSubsite
      (smallEtaleTopology X) (smallEtaleTopology X') := sorry

/-- Extending a small étale type sheaf to the spaces étale site and restricting
it back is isomorphic to the identity. -/
instance instIsIso_smallEtaleInclusion_sheafAdjunctionCocontinuous_counit
    (Y : AlgebraicSpace S) (F : Sheaf (smallEtaleTopology Y) (Type u)) :
    IsIso (((smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y)).counit.app F) :=
  sorry

/-- Extending a small étale type sheaf and restricting it back is the identity. -/
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

/-- The small étale pullback of a first-order thickening compares with
`etaleBaseChange` after inclusion into the spaces étale site. -/
def presentationEtalePullbackInclusionIso :
    presentationEtalePullback i ⋙ smallEtaleInclusion X ≅ etaleBaseChange i :=
  smallEtalePullbackCompInclusion i (presentationRepresentable i) ≪≫
    smallEtaleInclusion_comp_spacesEtalePullback i

/-- The composite of Lemma 76.9.6 with the small étale inclusion is continuous. -/
instance presentationEtalePullback_comp_inclusion_isContinuous :
    (presentationEtalePullback i ⋙ smallEtaleInclusion X).IsContinuous
      (smallEtaleTopology X') (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (presentationEtalePullback i) (smallEtaleInclusion X)
    (smallEtaleTopology X') (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Type-valued direct image along a first-order thickening agrees with
continuous pushforward of the small étale pullback. -/
def typePushforwardIsoPullback :
    typePushforward i ≅
      (presentationEtalePullback i).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology X') (smallEtaleTopology X) :=
  let extend :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let restrict :=
    (smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pull :=
    (presentationEtalePullback i).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X') (smallEtaleTopology X)
  isoWhiskerLeft extend
      ((sheafPushforwardContinuousIso (presentationEtalePullbackInclusionIso i)
          (Type u) (smallEtaleTopology X') (spacesEtaleTopology X)).symm ≪≫
        (sheafPushforwardContinuousComp (presentationEtalePullback i)
            (smallEtaleInclusion X) (Type u)
            (smallEtaleTopology X') (smallEtaleTopology X)
            (spacesEtaleTopology X)).symm) ≪≫
    Functor.associator extend restrict pull ≪≫
    isoWhiskerRight (smallEtaleInclusionCocontinuousContinuousIso X) pull ≪≫
    Functor.leftUnitor pull

/-- Inverse image of type-valued sheaves along a first-order thickening agrees
with continuous pushforward along the inverse of Lemma 76.9.6. -/
def typeInverseImageIso :
    (morphismOfTopoi i).inverseImage ≅
      (presentationEtalePullbackInverse i).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology X) (smallEtaleTopology X') :=
  Adjunction.leftAdjointUniq
    ((morphismOfTopoi i).adjunction.ofNatIsoRight (typePushforwardIsoPullback i))
    (Adjunction.sheafPushforwardContinuous
      (presentationEtalePullback i).asEquivalence.symm.toAdjunction
      (smallEtaleTopology X) (smallEtaleTopology X'))

/-- Transport of the universe-lifted structure sheaf of `X'` to `X_étale` along
Lemma 76.9.6. -/
def transportedStructureSheaf :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
      CommRingCat.{u + 1} (smallEtaleTopology X) (smallEtaleTopology X')).obj
    (commStructureSheafLift X')

/-- `transportedStructureSheaf i` is continuous pushforward of `𝒪_{X'}` along the
inverse of Lemma 76.9.6. -/
theorem transportedStructureSheaf_eq :
    transportedStructureSheaf i =
      ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
          CommRingCat.{u + 1} (smallEtaleTopology X) (smallEtaleTopology X')).obj
        (commStructureSheafLift X') :=
  rfl

/-- The underlying presheaf of the transported structure sheaf is precomposition
with the inverse of Lemma 76.9.6. -/
theorem transportedStructureSheaf_obj :
    (transportedStructureSheaf i).obj =
      (presentationEtalePullbackInverse i).op ⋙ (commStructureSheafLift X').obj :=
  rfl

/-- The unlifted transport of `𝒪_{X'}` along Lemma 76.9.6. -/
def transportedUnliftedSheaf : Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
      CommRingCat.{u} (smallEtaleTopology X) (smallEtaleTopology X')).obj
    (commStructureSheaf X')

/-- `transportedUnliftedSheaf i` is continuous pushforward of `𝒪_{X'}`. -/
theorem transportedUnliftedSheaf_eq :
    transportedUnliftedSheaf i =
      ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
          CommRingCat.{u} (smallEtaleTopology X) (smallEtaleTopology X')).obj
        (commStructureSheaf X') :=
  rfl

/-- Universe lift commutes with transport along Lemma 76.9.6, by presheaf
associators. -/
def transportedStructureSheafLiftIso :
    transportedStructureSheaf i ≅
      (sheafCompose (smallEtaleTopology X)
          CommRingCat.universeLift.{u, u + 1}).obj (transportedUnliftedSheaf i) :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) CommRingCat.{u + 1}).preimageIso
    ((isoWhiskerLeft (presentationEtalePullbackInverse i).op
        ((sheafToPresheaf (smallEtaleTopology X') CommRingCat.{u + 1}).mapIso
          (commStructureSheafComposeLiftIso X').symm)) ≪≫
      Functor.associator
        (presentationEtalePullbackInverse i).op
        (commStructureSheaf X').obj
        CommRingCat.universeLift.{u, u + 1} ≪≫
      isoWhiskerRight
        ((Functor.sheafPushforwardContinuousCompSheafToPresheafIso
            (presentationEtalePullbackInverse i) CommRingCat.{u}
            (smallEtaleTopology X) (smallEtaleTopology X')).symm.app
          (commStructureSheaf X'))
        CommRingCat.universeLift.{u, u + 1})

/-- Lift a type-valued map of forgotten commutative-ring sheaves to a morphism of
commutative-ring sheaves. -/
def commSheafHomOfTypeHom
    {R S : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (sheafCompose (smallEtaleTopology X)
            (CategoryTheory.forget CommRingCat.{u})).obj R ⟶
      (sheafCompose (smallEtaleTopology X)
            (CategoryTheory.forget CommRingCat.{u})).obj S) :
    R ⟶ S :=
  ⟨{ app := fun U ↦
        ConcreteCategory.ofHom (C := CommRingCat.{u})
          { toFun := ((sheafToPresheaf (smallEtaleTopology X) (Type u)).map φ).app U
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
     naturality := fun _ _ _ ↦ sorry }⟩

/-- Lift a type-valued isomorphism of forgotten commutative-ring sheaves to an
isomorphism of commutative-ring sheaves. -/
def commSheafIsoOfTypeIso
    {R S : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (e : (sheafCompose (smallEtaleTopology X)
            (CategoryTheory.forget CommRingCat.{u})).obj R ≅
      (sheafCompose (smallEtaleTopology X)
            (CategoryTheory.forget CommRingCat.{u})).obj S) :
    R ≅ S where
  hom := commSheafHomOfTypeHom e.hom
  inv := commSheafHomOfTypeHom e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forgetting the unlifted transport of `𝒪_{X'}` recovers continuous pushforward
of the forgotten structure sheaf. -/
def transportedUnliftedForgetIso :
    (sheafCompose (smallEtaleTopology X)
        (CategoryTheory.forget CommRingCat.{u})).obj (transportedUnliftedSheaf i) ≅
      ((presentationEtalePullbackInverse i).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology X) (smallEtaleTopology X')).obj
        ((sheafCompose (smallEtaleTopology X')
            (CategoryTheory.forget CommRingCat.{u})).obj (commStructureSheaf X')) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose
      (presentationEtalePullbackInverse i) (CategoryTheory.forget CommRingCat.{u})
      (smallEtaleTopology X) (smallEtaleTopology X')) |>.app (commStructureSheaf X')

/-- Forgetting `i⁻¹𝒪_{X'}` recovers inverse image of the forgotten structure
sheaf. -/
def inverseImageForgetIso :
    (sheafCompose (smallEtaleTopology X)
        (CategoryTheory.forget CommRingCat.{u})).obj
      (commInverseImageStructureSheaf i) ≅
      (morphismOfTopoi i).inverseImage.obj
        ((sheafCompose (smallEtaleTopology X')
            (CategoryTheory.forget CommRingCat.{u})).obj (commStructureSheaf X')) :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) (Type u)).preimageIso
    (Iso.refl _)

/-- The unlifted transport of `𝒪_{X'}` compares with `i⁻¹𝒪_{X'}` by lifting the
type-valued inverse-image comparison of Lemma 76.9.6. -/
def transportedUnliftedIso :
    transportedUnliftedSheaf i ≅ commInverseImageStructureSheaf i :=
  commSheafIsoOfTypeIso
    (transportedUnliftedForgetIso i ≪≫
      (typeInverseImageIso i).symm.app
        ((sheafCompose (smallEtaleTopology X')
            (CategoryTheory.forget CommRingCat.{u})).obj (commStructureSheaf X')) ≪≫
      (inverseImageForgetIso i).symm)

/-- Comparison of the transported structure sheaf with the inverse-image
presentation, by presheaf whiskering and fully faithful reflection, as in
`commStructureSheafComposeLiftIso`. -/
def transportedStructureSheafIso :
    transportedStructureSheaf i ≅ presentationSheaf i :=
  transportedStructureSheafLiftIso i ≪≫
    (sheafCompose (smallEtaleTopology X)
        CommRingCat.universeLift.{u, u + 1}).mapIso (transportedUnliftedIso i)

/-- The inverse-image presentation of `𝒪_{X'}`, viewed on `X'_étale` by
precomposition with Lemma 76.9.6. -/
def presentationPushedSheaf : Sheaf (smallEtaleTopology X') CommRingCat.{u + 1} :=
  ((presentationEtalePullback i).sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallEtaleTopology X') (smallEtaleTopology X)).obj (presentationSheaf i)

/-- `presentationPushedSheaf i` is the continuous pushforward of
`presentationSheaf i`. -/
theorem presentationPushedSheaf_eq :
    presentationPushedSheaf i =
      ((presentationEtalePullback i).sheafPushforwardContinuous CommRingCat.{u + 1}
          (smallEtaleTopology X') (smallEtaleTopology X)).obj
        (presentationSheaf i) :=
  rfl

/-- The ambient lifted structure sheaf of `X'` compares with the pushforward of
its transport along Lemma 76.9.6, by whiskering the unit of the site
equivalence and fully faithful reflection. -/
def presentationTransportedPushforwardIso :
    commStructureSheafLift X' ≅
      ((presentationEtalePullback i).sheafPushforwardContinuous CommRingCat.{u + 1}
          (smallEtaleTopology X') (smallEtaleTopology X)).obj
        (transportedStructureSheaf i) :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X') CommRingCat.{u + 1}).preimageIso
    ((Functor.leftUnitor (commStructureSheafLift X').obj).symm ≪≫
      isoWhiskerRight (presentationEtalePullback i).asEquivalence.op.unitIso
        (commStructureSheafLift X').obj ≪≫
      Functor.associator
        (presentationEtalePullback i).op
        (presentationEtalePullbackInverse i).op
        (commStructureSheafLift X').obj)

/-- The ambient lifted structure sheaf of `X'` compares with the pushforward of
the inverse-image presentation along the thickening equivalence. -/
def presentationPushedSheafIso :
    commStructureSheafLift X' ≅ presentationPushedSheaf i :=
  presentationTransportedPushforwardIso i ≪≫
    ((presentationEtalePullback i).sheafPushforwardContinuous CommRingCat.{u + 1}
        (smallEtaleTopology X') (smallEtaleTopology X)).mapIso
      (transportedStructureSheafIso i)

/-- The morphism of additive units sheaves induced by
`presentationPushedSheafIso i`. -/
def presentationUnitsSheafIso :
    Sheaf.unitsAddSheaf (commStructureSheafLift X') ≅
      Sheaf.unitsAddSheaf (presentationPushedSheaf i) where
  hom := Sheaf.unitsAddMap (presentationPushedSheafIso i).hom
  inv := Sheaf.unitsAddMap (presentationPushedSheafIso i).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Degree-zero units cohomology of `𝒪_{X'}` on `X'_étale` is identified with
that of the pushed inverse-image presentation. -/
def presentationUnitsH0PushedEquiv :
    (Sheaf.unitsAddSheaf (commStructureSheafLift X')).H 0 ≃+
      (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).H 0 where
  toFun := Sheaf.H.map (presentationUnitsSheafIso i).hom 0
  invFun := Sheaf.H.map (presentationUnitsSheafIso i).inv 0
  left_inv := sorry
  right_inv := sorry
  map_add' := (Sheaf.H.map (presentationUnitsSheafIso i).hom 0).map_add

/-- Equivalence of additive sheaf categories along Lemma 76.9.6. -/
def presentationAddSheafCongr :
    Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1} ≌
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (presentationEtalePullback i).asEquivalence.sheafCongr
    (smallEtaleTopology X') (smallEtaleTopology X) AddCommGrpCat.{u + 1}

/-- Sectionwise comparison of additive units of the pushed presentation with
the inverse image of presentation units along Lemma 76.9.6. -/
def presentationUnitsPushforwardCompareFunction (U : (smallEtaleSite X')ᵒᵖ) :
    (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U →
      ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U :=
  fun g ↦ Sheaf.unitsAddSheafSection (presentationSheaf i)
    (Sheaf.unitsAddSheafUnit (presentationPushedSheaf i) g)

/-- The inverse sectionwise comparison of additive units along Lemma 76.9.6. -/
def presentationUnitsPushforwardCompareInvFunction (U : (smallEtaleSite X')ᵒᵖ) :
    ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U →
      (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U :=
  fun g ↦ Sheaf.unitsAddSheafSection (presentationPushedSheaf i)
    (Sheaf.unitsAddSheafUnit (presentationSheaf i) g)

/-- Additive form of the sectionwise units comparison along Lemma 76.9.6. -/
def presentationUnitsPushforwardCompareHom (U : (smallEtaleSite X')ᵒᵖ) :
    (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U →+
      ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U where
  toFun := presentationUnitsPushforwardCompareFunction i U
  map_zero' := sorry
  map_add' := sorry

/-- Additive form of the inverse sectionwise units comparison along
Lemma 76.9.6. -/
def presentationUnitsPushforwardCompareInvHom (U : (smallEtaleSite X')ᵒᵖ) :
    ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U →+
      (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U where
  toFun := presentationUnitsPushforwardCompareInvFunction i U
  map_zero' := sorry
  map_add' := sorry

/-- Identifying units of the pushed presentation sheaf with the inverse image of
the presentation units sheaf along Lemma 76.9.6, by the public units-section
conversion on the common ring objects. -/
def presentationUnitsPushforwardCompare :
    Sheaf.unitsAddSheaf (presentationPushedSheaf i) ≅
      (presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i)) where
  hom := ⟨{ app := fun U ↦
              AddCommGrpCat.ofHom (presentationUnitsPushforwardCompareHom i U)
            naturality := fun {_ _} _ ↦ sorry }⟩
  inv := ⟨{ app := fun U ↦
              AddCommGrpCat.ofHom (presentationUnitsPushforwardCompareInvHom i U)
            naturality := fun {_ _} _ ↦ sorry }⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical sheaf morphism from the constant abelian sheaf on `X_étale` to
the transport of the constant abelian sheaf on `X'_étale` along Lemma 76.9.6. -/
def presentationConstantCompareInv :
    (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (presentationAddSheafCongr i).functor.obj
        ((constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) :=
  ((sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))
      ((presentationAddSheafCongr i).functor.obj
        ((constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))))).symm
    ((Functor.constCompWhiskeringLeftIso (smallEtaleSite X)ᵒᵖ
        (presentationEtalePullbackInverse i).op).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
      Functor.whiskerLeft (presentationEtalePullbackInverse i).op
        ((sheafificationAdjunction (smallEtaleTopology X') AddCommGrpCat.{u + 1}).unit.app
          ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))))

/-- The canonical sheaf morphism from the constant abelian sheaf on `X'_étale` to
the inverse transport of the constant abelian sheaf on `X_étale`. -/
def presentationConstantCompareSwappedInv :
    (constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (presentationAddSheafCongr i).inverse.obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) :=
  ((sheafificationAdjunction (smallEtaleTopology X') AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))
      ((presentationAddSheafCongr i).inverse.obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))))).symm
    ((Functor.constCompWhiskeringLeftIso (smallEtaleSite X')ᵒᵖ
        (presentationEtalePullback i).op).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
      Functor.whiskerLeft (presentationEtalePullback i).op
        ((sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u + 1}).unit.app
          ((Functor.const _).obj (AddCommGrpCat.of (ULift ℤ)))))

/-- The forward constant-sheaf comparison along Lemma 76.9.6. -/
def presentationConstantCompareHom :
    (presentationAddSheafCongr i).functor.obj
        ((constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift ℤ))) ⟶
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (presentationAddSheafCongr i).functor.map (presentationConstantCompareSwappedInv i) ≫
    (presentationAddSheafCongr i).counitIso.hom.app
      ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)))

/-- Constant abelian sheaves are preserved by Lemma 76.9.6. -/
def presentationConstantCompare :
    (presentationAddSheafCongr i).functor.obj
      ((constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) ≅
    (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) where
  hom := presentationConstantCompareHom i
  inv := presentationConstantCompareInv i
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Degree-zero cohomology of the pushed presentation units is identified with
degree-zero cohomology of the inverse-image presentation units, via the
equivalence of Lemma 76.9.6. -/
def presentationUnitsH0SiteEquiv :
    (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).H 0 ≃+
      (Sheaf.unitsAddSheaf (presentationSheaf i)).H 0 where
  toFun x :=
    (Ext.addEquiv₀).symm
      ((presentationConstantCompare i).inv ≫
        (presentationAddSheafCongr i).functor.map
          (Ext.addEquiv₀ x ≫ (presentationUnitsPushforwardCompare i).hom) ≫
        (presentationAddSheafCongr i).counitIso.hom.app
          (Sheaf.unitsAddSheaf (presentationSheaf i)))
  invFun y :=
    (Ext.addEquiv₀).symm
      ((presentationAddSheafCongr i).unitIso.hom.app
          ((constantSheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift ℤ))) ≫
        (presentationAddSheafCongr i).inverse.map
          ((presentationConstantCompare i).hom ≫ Ext.addEquiv₀ y) ≫
        (presentationUnitsPushforwardCompare i).inv)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- Degree-zero units cohomology of the ambient thickening is identified with
degree-zero cohomology of units of the inverse-image presentation. -/
def presentationUnitsH0Equiv :
    (Sheaf.unitsAddSheaf (commStructureSheafLift X')).H 0 ≃+
      (Sheaf.unitsAddSheaf (presentationSheaf i)).H 0 :=
  (presentationUnitsH0PushedEquiv i).trans (presentationUnitsH0SiteEquiv i)

/-- `presentationUnitsH0Equiv i` is the composite of the pushed units comparison
with the Lemma 76.9.6 site identification. -/
theorem presentationUnitsH0Equiv_eq :
    presentationUnitsH0Equiv i =
      (presentationUnitsH0PushedEquiv i).trans (presentationUnitsH0SiteEquiv i) :=
  rfl

/-- Restriction of scalars along the inverse-image presentation preserves
invertibility. -/
instance presentationRestriction_isInvertible
    (L : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (commStructureSheafLift X))
    [isInvertibleObject L] :
    isInvertibleObject
      ((restrictionAlong.{u + 1, u, u + 1, u + 1} (presentationProjection i)).obj L) :=
  sorry

/-- An `𝒪_{X'}`-module pulled back to `X` and restricted along the inverse-image
presentation `i⁻¹𝒪_{X'} ⟶ 𝒪_X`. -/
def presentationLiftModule (L : X'.Modules) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (presentationSheaf i) :=
  (restrictionAlong.{u + 1, u, u + 1, u + 1} (presentationProjection i)).obj
    (Modules.liftModule ((Modules.pullback i).obj L))

/-- `presentationLiftModule i L` is restriction of scalars of the universe lift
of the module pullback of `L`. -/
theorem presentationLiftModule_eq (L : X'.Modules) :
    presentationLiftModule i L =
      (restrictionAlong.{u + 1, u, u + 1, u + 1} (presentationProjection i)).obj
        (Modules.liftModule ((Modules.pullback i).obj L)) :=
  rfl

/-- Invertibility is preserved by transport to the inverse-image presentation. -/
instance presentationLiftModule_isInvertible (L : X'.Modules)
    [isInvertibleObject L] :
    isInvertibleObject (presentationLiftModule i L) := sorry

/-- The canonical additive comparison from Picard classes of `X'` to Picard
classes of the inverse-image presentation. -/
def presentationPicardMap :
    X'.PicardGroup →+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology X)
        (presentationSheaf i) where
  toFun x :=
    MonoidalCategory.PicardGroup.mk (presentationLiftModule i (PicardGroup.repr x))
  map_zero' := sorry
  map_add' := sorry

/-- `presentationPicardMap i` sends a class to the class of its presentation
lift. -/
theorem presentationPicardMap_apply (x : X'.PicardGroup) :
    presentationPicardMap i x =
      MonoidalCategory.PicardGroup.mk
        (presentationLiftModule i (PicardGroup.repr x)) := sorry

/-- The underlying inverse function of `presentationPicardMap i`. -/
def presentationPicardInverseFunction :
    SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology X)
      (presentationSheaf i) → X'.PicardGroup :=
  Function.invFun (presentationPicardMap i)

/-- The inverse comparison sends zero to zero. -/
theorem presentationPicardInverseFunction_zero :
    presentationPicardInverseFunction i 0 = 0 := sorry

/-- The inverse comparison is additive. -/
theorem presentationPicardInverseFunction_add
    (x y : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology X)
      (presentationSheaf i)) :
    presentationPicardInverseFunction i (x + y) =
      presentationPicardInverseFunction i x +
        presentationPicardInverseFunction i y := sorry

/-- Transport followed by its inverse recovers an ambient Picard class. -/
theorem presentationPicardMap_leftInverse (x : X'.PicardGroup) :
    presentationPicardInverseFunction i (presentationPicardMap i x) = x := sorry

/-- The inverse transport followed by forward transport recovers a presentation
Picard class. -/
theorem presentationPicardMap_rightInverse
    (x : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology X)
      (presentationSheaf i)) :
    presentationPicardMap i (presentationPicardInverseFunction i x) = x := sorry

/-- The canonical additive equivalence between the universe-lifted Picard group
of `X'` and the Picard group of its inverse-image presentation. -/
def presentationPicardEquiv :
    ULift.{u + 2, u + 1} X'.PicardGroup ≃+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology X)
        (presentationSheaf i) where
  toFun x := presentationPicardMap i x.down
  invFun y := ULift.up (presentationPicardInverseFunction i y)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- Universe lift of an algebraic-space Picard class to the Picard group of the
lifted commutative structure sheaf. -/
def structurePicardMap (Y : AlgebraicSpace S) :
    Y.PicardGroup →+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
        (commStructureSheafLift Y) where
  toFun x :=
    MonoidalCategory.PicardGroup.mk (Modules.liftModule (PicardGroup.repr x))
  map_zero' := sorry
  map_add' := sorry

/-- `structurePicardMap Y` is computed by lifting a chosen representative. -/
theorem structurePicardMap_apply (Y : AlgebraicSpace S) (x : Y.PicardGroup) :
    structurePicardMap Y x =
      MonoidalCategory.PicardGroup.mk (Modules.liftModule (PicardGroup.repr x)) :=
  sorry

/-- The underlying inverse function of `structurePicardMap Y`. -/
def structurePicardInverseFunction (Y : AlgebraicSpace S) :
    SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y) → Y.PicardGroup :=
  Function.invFun (structurePicardMap Y)

/-- The inverse structure-Picard comparison sends zero to zero. -/
theorem structurePicardInverseFunction_zero (Y : AlgebraicSpace S) :
    structurePicardInverseFunction Y 0 = 0 := sorry

/-- The inverse structure-Picard comparison is additive. -/
theorem structurePicardInverseFunction_add (Y : AlgebraicSpace S)
    (x y : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y)) :
    structurePicardInverseFunction Y (x + y) =
      structurePicardInverseFunction Y x + structurePicardInverseFunction Y y :=
  sorry

/-- The structure-Picard comparison followed by its inverse recovers an ambient
Picard class. -/
theorem structurePicardMap_leftInverse (Y : AlgebraicSpace S)
    (x : Y.PicardGroup) :
    structurePicardInverseFunction Y (structurePicardMap Y x) = x := sorry

/-- The inverse structure-Picard comparison followed by the forward comparison
recovers a lifted Picard class. -/
theorem structurePicardMap_rightInverse (Y : AlgebraicSpace S)
    (x : SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
      (commStructureSheafLift Y)) :
    structurePicardMap Y (structurePicardInverseFunction Y x) = x := sorry

/-- The canonical additive equivalence between the Picard group of an algebraic
space and the Picard group of its universe-lifted commutative structure sheaf. -/
def structurePicardEquiv (Y : AlgebraicSpace S) :
    ULift.{u + 2, u + 1} Y.PicardGroup ≃+
      SheafOfModules.RingedSite.PicardGroup (smallEtaleTopology Y)
        (commStructureSheafLift Y) where
  toFun x := structurePicardMap Y x.down
  invFun y := ULift.up (structurePicardInverseFunction Y y)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The units short complex `I ⟶ 𝒪_{X'}ˣ ⟶ 𝒪_Xˣ` of the inverse-image
presentation, with first map `x ↦ 1 + x`. -/
def unitsShortComplex :
    ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  KernelIdeal.unitsShortComplex.{u + 1, u} (presentationProjection i)
    (presentationKernel_isSquareZero i)

/-- The first map of `unitsShortComplex i` is `x ↦ 1 + x`. -/
theorem unitsShortComplex_f :
    (unitsShortComplex i).f =
      KernelIdeal.oneAdd.{u + 1, u} (presentationProjection i)
        (presentationKernel_isSquareZero i) := sorry

/-- The second map of `unitsShortComplex i` is the map on units induced by
`presentationProjection i`. -/
theorem unitsShortComplex_g :
    (unitsShortComplex i).g = unitsAddMap (presentationProjection i) := sorry

/-- Local surjectivity of the presentation projection makes the units short
complex short exact. -/
theorem unitsShortComplex_shortExact :
    (unitsShortComplex i).ShortExact := sorry

/-- The six-object cohomology window of the units short complex in degrees
`n` and `n + 1`. -/
def unitsWindow (n : ℕ) : ComposableArrows AddCommGrpCat.{u + 2} 5 :=
  KernelIdeal.unitsCohomologyWindow.{u + 1, u} (presentationProjection i)
    (presentationKernel_isSquareZero i) (unitsShortComplex_shortExact i) n

/-- Adjacent maps in `unitsWindow i n` form an exact sequence. -/
theorem unitsWindow_exact (n : ℕ) : (unitsWindow i n).Exact := sorry

/-- Universe alignment of an algebraic-space Picard group with the lifted
étale cohomology sequence. -/
def picardULift (Y : AlgebraicSpace S) :
    ULift.{u + 2, u + 1} Y.PicardGroup ≃+ Y.PicardGroup :=
  AddEquiv.ulift

/-- The map `H¹(I) ⟶ Pic(X')` obtained by the units connecting morphism into
`Pic` of the presentation, transported along `presentationPicardEquiv`. -/
def toPicard :
    AddCommGrpCat.of ((presentationKernelAdditive i).H 1) ⟶
      AddCommGrpCat.of (ULift.{u + 2, u + 1} X'.PicardGroup) :=
  let π := presentationProjection i
  let hzero := presentationKernel_isSquareZero i
  let hS := unitsShortComplex_shortExact i
  KernelIdeal.toPicard.{u + 1, u} π hzero hS ≫
    AddCommGrpCat.ofHom (presentationPicardEquiv i).symm.toAddMonoidHom

/-- The Picard map of the cohomology sequence is pullback along the original
first-order thickening. -/
def picardMap :
    AddCommGrpCat.of (ULift.{u + 2, u + 1} X'.PicardGroup) ⟶
      AddCommGrpCat.of (ULift.{u + 2, u + 1} X.PicardGroup) :=
  AddCommGrpCat.ofHom
    (((picardULift X).symm.toAddMonoidHom.comp (picardPullback i)).comp
      (picardULift X').toAddMonoidHom)

/-- `picardMap i` is the universe-aligned form of `picardPullback i`. -/
theorem picardMap_eq :
    picardMap i =
      AddCommGrpCat.ofHom
        (((picardULift X).symm.toAddMonoidHom.comp (picardPullback i)).comp
          (picardULift X').toAddMonoidHom) :=
  rfl

/-- The map `Pic(X) ⟶ H²(I)` obtained by applying the next connecting morphism
after the Picard-units comparison of the lifted structure sheaf. -/
def fromPicard :
    AddCommGrpCat.of (ULift.{u + 2, u + 1} X.PicardGroup) ⟶
      AddCommGrpCat.of ((presentationKernelAdditive i).H 2) :=
  let π := presentationProjection i
  let hzero := presentationKernel_isSquareZero i
  let hS := unitsShortComplex_shortExact i
  AddCommGrpCat.ofHom (structurePicardEquiv X).toAddMonoidHom ≫
    KernelIdeal.fromPicard.{u + 1, u} π hzero hS

/-- The canonical eight-object Picard cohomology row
`0 ⟶ H⁰(I) ⟶ H⁰(𝒪_{X'}ˣ) ⟶ H⁰(𝒪_Xˣ) ⟶ H¹(I) ⟶ Pic(X') ⟶ Pic(X) ⟶ H²(I)`
of a first-order thickening of algebraic spaces. -/
def picardCohomologySequence : ComposableArrows AddCommGrpCat.{u + 2} 7 :=
  let π := presentationProjection i
  let hzero := presentationKernel_isSquareZero i
  let hS := unitsShortComplex_shortExact i
  let s := KernelIdeal.picardCohomologySequence.{u + 1, u} π hzero hS
  let eUnits := presentationUnitsH0Equiv i
  ((ComposableArrows.mk₅
      (AddCommGrpCat.ofHom eUnits.toAddMonoidHom ≫ s.map' 2 3)
      (s.map' 3 4) (toPicard i) (picardMap i) (fromPicard i)).precomp
    (s.map' 1 2 ≫ AddCommGrpCat.ofHom eUnits.symm.toAddMonoidHom)).precomp
      (s.map' 0 1)

/-- The first arrow of the Picard cohomology row is the zero map into
`H⁰(I)`. -/
theorem picardCohomologySequence_map_zero :
    (picardCohomologySequence i).map' 0 1 =
      (0 : ⊥_ AddCommGrpCat.{u + 2} ⟶
        AddCommGrpCat.of ((presentationKernelAdditive i).H 0)) := sorry

/-- The second arrow of the Picard cohomology row is `x ↦ 1 + x` conjugated to
ambient `H⁰(X', 𝒪_{X'}ˣ)`. -/
theorem picardCohomologySequence_map_one :
    (picardCohomologySequence i).map' 1 2 =
      (unitsWindow i 0).map' 0 1 ≫
        AddCommGrpCat.ofHom (presentationUnitsH0Equiv i).symm.toAddMonoidHom := sorry

/-- The third arrow of the Picard cohomology row is the degree-zero map on units
induced by the presentation projection, conjugated from ambient
`H⁰(X', 𝒪_{X'}ˣ)`. -/
theorem picardCohomologySequence_map_two :
    (picardCohomologySequence i).map' 2 3 =
      AddCommGrpCat.ofHom (presentationUnitsH0Equiv i).toAddMonoidHom ≫
        (unitsWindow i 0).map' 1 2 := sorry

/-- The fourth arrow of the Picard cohomology row is the first connecting
morphism. -/
theorem picardCohomologySequence_map_three :
    (picardCohomologySequence i).map' 3 4 = (unitsWindow i 0).map' 2 3 := sorry

/-- The fifth arrow of the Picard cohomology row is the transported map from
`H¹(I)` to `Pic(X')`. -/
theorem picardCohomologySequence_map_four :
    (picardCohomologySequence i).map' 4 5 = toPicard i := sorry

/-- The sixth arrow of the Picard cohomology row is pullback of Picard groups
along `i`. -/
theorem picardCohomologySequence_map_five :
    (picardCohomologySequence i).map' 5 6 = picardMap i := sorry

/-- The seventh arrow of the Picard cohomology row is the transported second
connecting morphism. -/
theorem picardCohomologySequence_map_six :
    (picardCohomologySequence i).map' 6 7 = fromPicard i := sorry

/-- The Picard cohomology row of a first-order thickening of algebraic spaces is
exact. -/
theorem picardCohomologySequence_exact :
    (picardCohomologySequence i).Exact := sorry

/-- The Picard arrow in the cohomology row is pullback along the original
first-order thickening. -/
theorem picardCohomologySequence_picardMap (x : X'.PicardGroup) :
    ((picardCohomologySequence i).map' 5 6).hom (ULift.up x) =
      ULift.up (picardPullback i x) := sorry

/-- The map `toPicard i` is the units connecting morphism followed by the
inverse of the presentation Picard equivalence. -/
theorem toPicard_eq :
    toPicard i =
      KernelIdeal.toPicard.{u + 1, u} (presentationProjection i)
          (presentationKernel_isSquareZero i) (unitsShortComplex_shortExact i) ≫
        AddCommGrpCat.ofHom (presentationPicardEquiv i).symm.toAddMonoidHom :=
  rfl

/-- The map `fromPicard i` is the structure-Picard comparison followed by the
degree-two connecting morphism. -/
theorem fromPicard_eq :
    fromPicard i =
      AddCommGrpCat.ofHom (structurePicardEquiv X).toAddMonoidHom ≫
        KernelIdeal.fromPicard.{u + 1, u} (presentationProjection i)
          (presentationKernel_isSquareZero i) (unitsShortComplex_shortExact i) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
