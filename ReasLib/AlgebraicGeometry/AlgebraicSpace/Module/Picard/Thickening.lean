/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.SquareZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientEquivalence
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.LocallyRinged
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder.Presentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sheaf CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open CategoryTheory.Abelian

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsFirstOrderThickening i]

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
variable [hExt : HasExt.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [hExt' : HasExt.{u + 2} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]

/-- Base change along a first-order thickening, as a functor of small étale
sites. -/
abbrev presentationEtalePullback : smallEtaleSite X' ⥤ smallEtaleSite X :=
  smallEtalePullback i (IsIntegralHom.relativelyRepresentable i)

/-- Base change along a first-order thickening is continuous for the small étale
topologies. -/
instance presentationEtalePullback_isContinuous :
    (presentationEtalePullback i).IsContinuous
      (smallEtaleTopology X') (smallEtaleTopology X) := sorry

/-- The inverse of the thickening étale-site equivalence, as a functor of small étale sites. -/
abbrev presentationEtalePullbackInverse : smallEtaleSite X ⥤ smallEtaleSite X' :=
  (presentationEtalePullback i).asEquivalence.inverse

/-- The inverse of the thickening étale-site equivalence is continuous for the small étale topologies. -/
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

/-- The inverse of the thickening étale-site equivalence is a dense subsite functor. -/
instance presentationEtalePullbackInverse_isDenseSubsite :
    (presentationEtalePullback i).asEquivalence.inverse.IsDenseSubsite
      (smallEtaleTopology X) (smallEtaleTopology X') := sorry

/-- The small étale pullback of a first-order thickening compares with
`etaleBaseChange` after inclusion into the spaces étale site. -/
def presentationEtalePullbackInclusionIso :
    presentationEtalePullback i ⋙ smallEtaleToSpaces X ≅ etaleBaseChange i :=
  smallEtalePullbackCompInclusion i (IsIntegralHom.relativelyRepresentable i) ≪≫
    smallEtaleInclusion_comp_spacesEtalePullback i

/-- The composite of the thickening étale-site equivalence with the small étale inclusion is continuous. -/
instance presentationEtalePullback_comp_inclusion_isContinuous :
    (presentationEtalePullback i ⋙ smallEtaleToSpaces X).IsContinuous
      (smallEtaleTopology X') (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (presentationEtalePullback i) (smallEtaleToSpaces X)
    (smallEtaleTopology X') (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Type-valued direct image along a first-order thickening agrees with
continuous pushforward of the small étale pullback. -/
def typePushforwardIsoPullback :
    EtaleTopos.directImage i ≅
      (presentationEtalePullback i).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology X') (smallEtaleTopology X) :=
  let extend := EtaleTopos.extension X
  let restrict := EtaleTopos.restriction X
  let pull :=
    (presentationEtalePullback i).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X') (smallEtaleTopology X)
  isoWhiskerLeft extend
      ((sheafPushforwardContinuousIso (presentationEtalePullbackInclusionIso i)
          (Type u) (smallEtaleTopology X') (spacesEtaleTopology X)).symm ≪≫
        (sheafPushforwardContinuousComp (presentationEtalePullback i)
            (smallEtaleToSpaces X) (Type u)
            (smallEtaleTopology X') (smallEtaleTopology X)
            (spacesEtaleTopology X)).symm) ≪≫
    Functor.associator extend restrict pull ≪≫
    isoWhiskerRight (EtaleTopos.extensionRestrictionIso X) pull ≪≫
    Functor.leftUnitor pull

/-- Inverse image of type-valued sheaves along a first-order thickening agrees
with continuous pushforward along the inverse of the thickening étale-site equivalence. -/
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
the thickening étale-site equivalence. -/
def transportedStructureSheaf :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
      CommRingCat.{u + 1} (smallEtaleTopology X) (smallEtaleTopology X')).obj
    (commStructureSheafLift X')

/-- The underlying presheaf of the transported structure sheaf is precomposition
with the inverse of the thickening étale-site equivalence. -/
theorem transportedStructureSheaf_obj :
    (transportedStructureSheaf i).obj =
      (presentationEtalePullbackInverse i).op ⋙ (commStructureSheafLift X').obj :=
  rfl

/-- The unlifted transport of `𝒪_{X'}` along the thickening étale-site equivalence. -/
def transportedUnliftedSheaf : Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  ((presentationEtalePullbackInverse i).sheafPushforwardContinuous
      CommRingCat.{u} (smallEtaleTopology X) (smallEtaleTopology X')).obj
    (commStructureSheaf X')

/-- Universe lift commutes with transport along the thickening étale-site equivalence, by presheaf
associators. -/
def transportedStructureSheafLiftIso :
    transportedStructureSheaf i ≅
      (sheafCompose (smallEtaleTopology X)
          CommRingCat.universeLift.{u, u + 1}).obj (transportedUnliftedSheaf i) :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) CommRingCat.{u + 1}).preimageIso
    ((isoWhiskerLeft (presentationEtalePullbackInverse i).op
        ((sheafToPresheaf (smallEtaleTopology X') CommRingCat.{u + 1}).mapIso
          (commStructureSheafComposeLiftIso X').symm)) ≪≫
      Functor.associator (presentationEtalePullbackInverse i).op
        (commStructureSheaf X').obj CommRingCat.universeLift.{u, u + 1} ≪≫
      isoWhiskerRight
        ((Functor.sheafPushforwardContinuousCompSheafToPresheafIso
            (presentationEtalePullbackInverse i) CommRingCat.{u}
            (smallEtaleTopology X) (smallEtaleTopology X')).symm.app
          (commStructureSheaf X'))
        CommRingCat.universeLift.{u, u + 1})

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

/-- The underlying type-sheaf comparison between transported coefficients and inverse-image coefficients. -/
def transportedUnliftedTypeIso :
    (commRingUnderlying X).obj (transportedUnliftedSheaf i) ≅
      (commRingUnderlying X).obj (commInverseImageStructureSheaf i) :=
  transportedUnliftedForgetIso i ≪≫
    (typeInverseImageIso i).symm.app
      ((sheafCompose (smallEtaleTopology X')
          (CategoryTheory.forget CommRingCat.{u})).obj (commStructureSheaf X')) ≪≫
    (inverseImageForgetIso i).symm

/-- The forward and inverse coefficient comparisons preserve zero in their respective rings. -/
theorem transportedUnliftedTypeIso_map_zero :
    (∀ U, (transportedUnliftedTypeIso i).hom.hom.app U (0 : (transportedUnliftedSheaf i).obj.obj U) =
      (0 : (commInverseImageStructureSheaf i).obj.obj U)) ∧
    (∀ U, (transportedUnliftedTypeIso i).inv.hom.app U (0 : (commInverseImageStructureSheaf i).obj.obj U) =
      (0 : (transportedUnliftedSheaf i).obj.obj U)) := sorry

/-- The forward and inverse coefficient comparisons preserve one in their respective rings. -/
theorem transportedUnliftedTypeIso_map_one :
    (∀ U, (transportedUnliftedTypeIso i).hom.hom.app U (1 : (transportedUnliftedSheaf i).obj.obj U) =
      (1 : (commInverseImageStructureSheaf i).obj.obj U)) ∧
    (∀ U, (transportedUnliftedTypeIso i).inv.hom.app U (1 : (commInverseImageStructureSheaf i).obj.obj U) =
      (1 : (transportedUnliftedSheaf i).obj.obj U)) := sorry

/-- The forward and inverse coefficient comparisons preserve addition in their respective rings. -/
theorem transportedUnliftedTypeIso_map_add :
    (∀ U (r s : (transportedUnliftedSheaf i).obj.obj U),
      (transportedUnliftedTypeIso i).hom.hom.app U (r + s) =
        ((inferInstance : Add ((commInverseImageStructureSheaf i).obj.obj U)).add
          ((transportedUnliftedTypeIso i).hom.hom.app U r) ((transportedUnliftedTypeIso i).hom.hom.app U s) :
            (commInverseImageStructureSheaf i).obj.obj U)) ∧
    (∀ U (r s : (commInverseImageStructureSheaf i).obj.obj U),
      (transportedUnliftedTypeIso i).inv.hom.app U (r + s) =
        ((inferInstance : Add ((transportedUnliftedSheaf i).obj.obj U)).add
          ((transportedUnliftedTypeIso i).inv.hom.app U r) ((transportedUnliftedTypeIso i).inv.hom.app U s) :
            (transportedUnliftedSheaf i).obj.obj U)) := sorry

/-- The forward and inverse coefficient comparisons preserve multiplication in their respective rings. -/
theorem transportedUnliftedTypeIso_map_mul :
    (∀ U (r s : (transportedUnliftedSheaf i).obj.obj U),
      (transportedUnliftedTypeIso i).hom.hom.app U (r * s) =
        ((inferInstance : Mul ((commInverseImageStructureSheaf i).obj.obj U)).mul
          ((transportedUnliftedTypeIso i).hom.hom.app U r) ((transportedUnliftedTypeIso i).hom.hom.app U s) :
            (commInverseImageStructureSheaf i).obj.obj U)) ∧
    (∀ U (r s : (commInverseImageStructureSheaf i).obj.obj U),
      (transportedUnliftedTypeIso i).inv.hom.app U (r * s) =
        ((inferInstance : Mul ((transportedUnliftedSheaf i).obj.obj U)).mul
          ((transportedUnliftedTypeIso i).inv.hom.app U r) ((transportedUnliftedTypeIso i).inv.hom.app U s) :
            (transportedUnliftedSheaf i).obj.obj U)) := sorry

/-- The transported coefficient ring is isomorphic to the inverse-image coefficient ring by the underlying comparison functions. -/
def transportedUnliftedIso :
    transportedUnliftedSheaf i ≅ commInverseImageStructureSheaf i where
  hom := commRingHomOfUnderlying (transportedUnliftedTypeIso i).hom
    (transportedUnliftedTypeIso_map_zero i).1 (transportedUnliftedTypeIso_map_one i).1
    (transportedUnliftedTypeIso_map_add i).1 (transportedUnliftedTypeIso_map_mul i).1
  inv := commRingHomOfUnderlying (transportedUnliftedTypeIso i).inv
    (transportedUnliftedTypeIso_map_zero i).2 (transportedUnliftedTypeIso_map_one i).2
    (transportedUnliftedTypeIso_map_add i).2 (transportedUnliftedTypeIso_map_mul i).2
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Comparison of the transported structure sheaf with the inverse-image
presentation, by presheaf whiskering and fully faithful reflection, as in
`commStructureSheafComposeLiftIso`. -/
def transportedStructureSheafIso :
    transportedStructureSheaf i ≅ presentationSheaf i :=
  transportedStructureSheafLiftIso i ≪≫
    (sheafCompose (smallEtaleTopology X)
        CommRingCat.universeLift.{u, u + 1}).mapIso (transportedUnliftedIso i)

/-- The inverse-image presentation of `𝒪_{X'}`, viewed on `X'_étale` by
precomposition with the thickening étale-site equivalence. -/
def presentationPushedSheaf : Sheaf (smallEtaleTopology X') CommRingCat.{u + 1} :=
  ((presentationEtalePullback i).sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallEtaleTopology X') (smallEtaleTopology X)).obj (presentationSheaf i)

/-- The ambient lifted structure sheaf of `X'` compares with the pushforward of
its transport along the thickening étale-site equivalence, by whiskering the unit of the site
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
      Functor.associator (presentationEtalePullback i).op
        (presentationEtalePullbackInverse i).op (commStructureSheafLift X').obj)

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

/-- Equivalence of additive sheaf categories along the thickening étale-site equivalence. -/
def presentationAddSheafCongr :
    Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1} ≌
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (presentationEtalePullback i).asEquivalence.sheafCongr
    (smallEtaleTopology X') (smallEtaleTopology X) AddCommGrpCat.{u + 1}

/-- Sectionwise comparison of additive units of the pushed presentation with
the inverse image of presentation units along the thickening étale-site equivalence. -/
def presentationUnitsPushforwardCompareFunction (U : (smallEtaleSite X')ᵒᵖ) :
    (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U →
      ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U :=
  fun g ↦ Sheaf.unitsAddSheafSection (presentationSheaf i)
    (Sheaf.unitsAddSheafUnit (presentationPushedSheaf i) g)

/-- The inverse sectionwise comparison of additive units along the thickening étale-site equivalence. -/
def presentationUnitsPushforwardCompareInvFunction (U : (smallEtaleSite X')ᵒᵖ) :
    ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U →
      (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U :=
  fun g ↦ Sheaf.unitsAddSheafSection (presentationPushedSheaf i)
    (Sheaf.unitsAddSheafUnit (presentationSheaf i) g)

/-- Additive form of the sectionwise units comparison along the thickening étale-site equivalence. -/
def presentationUnitsPushforwardCompareHom (U : (smallEtaleSite X')ᵒᵖ) :
    (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U →+
      ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U where
  toFun := presentationUnitsPushforwardCompareFunction i U
  map_zero' := sorry
  map_add' := sorry

/-- Additive form of the inverse sectionwise units comparison along
the thickening étale-site equivalence. -/
def presentationUnitsPushforwardCompareInvHom (U : (smallEtaleSite X')ᵒᵖ) :
    ((presentationAddSheafCongr i).inverse.obj
        (Sheaf.unitsAddSheaf (presentationSheaf i))).1.obj U →+
      (Sheaf.unitsAddSheaf (presentationPushedSheaf i)).1.obj U where
  toFun := presentationUnitsPushforwardCompareInvFunction i U
  map_zero' := sorry
  map_add' := sorry

/-- Identifying units of the pushed presentation sheaf with the inverse image of
the presentation units sheaf along the thickening étale-site equivalence, by the public units-section
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
the transport of the constant abelian sheaf on `X'_étale` along the thickening étale-site equivalence. -/
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

/-- The forward constant-sheaf comparison along the thickening étale-site equivalence. -/
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

/-- Constant abelian sheaves are preserved by the thickening étale-site equivalence. -/
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
equivalence of the thickening étale-site equivalence. -/
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

/-- Modules over the ambient lifted structure sheaf transport along the inverse étale-site equivalence and its coefficient isomorphism. -/
def presentationModuleEquivalence :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X') (commStructureSheafLift X') ≌
      ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (presentationSheaf i) :=
  SheafOfModules.CoefficientEquivalence.equivalence
    (presentationEtalePullback i).asEquivalence.symm
    ((sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (transportedStructureSheafIso i).symm)

/-- An ambient module is universe lifted and transported to the inverse-image coefficient presentation. -/
def presentationLiftModule (L : X'.Modules) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (presentationSheaf i) :=
  (presentationModuleEquivalence i).functor.obj (Modules.liftModule L)

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
    (((AddEquiv.ulift : ULift.{u + 2, u + 1} X.PicardGroup ≃+ X.PicardGroup).symm.toAddMonoidHom.comp (picardPullback i)).comp
      (AddEquiv.ulift : ULift.{u + 2, u + 1} X'.PicardGroup ≃+ X'.PicardGroup).toAddMonoidHom)

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

/-- The cohomological Picard map agrees with geometric pullback under the ambient coefficient comparisons. -/
theorem presentationPicardEquiv_pullback :
    AddCommGrpCat.ofHom (presentationPicardEquiv i).toAddMonoidHom ≫
        KernelIdeal.picardMap.{u + 1, u} (presentationProjection i)
          (presentationKernel_isSquareZero i) (unitsShortComplex_shortExact i) =
      picardMap i ≫ AddCommGrpCat.ofHom (structurePicardEquiv X).toAddMonoidHom := sorry

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

/-- The Picard cohomology row and every higher units cohomology window of a first-order thickening are exact. -/
theorem picardCohomologySequence_longExact :
    (picardCohomologySequence i).Exact ∧ ∀ n : ℕ, (unitsWindow i n).Exact := sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
