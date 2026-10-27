/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Homotopy

/-! # Derived module comparison for the total étale augmentation -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

/-- The additive right Kan extensions from the actual affine charts exist. -/
private instance spacesAdditiveKanLimits {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : (spacesEtaleSite X)ᵒᵖ) :
    CategoryTheory.Limits.HasLimitsOfShape
      (StructuredArrow V (SpacesEtale.AtlasCharts.inclusion X).op) AddCommGrpCat.{u} :=
  CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Abelian sheaves on the spaces-étale site admit sheafification in the coefficient universe. -/
instance hasSheafifySpaces {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasSheafify (spacesRingedSite X).siteTopology AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)
    (SpacesEtale.AtlasCharts.inclusion X)

/-- Sheafification equivalences on the spaces-étale site are the locally bijective maps. -/
instance locallyBijectiveSpaces {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesRingedSite X).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u} := sorry

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Module direct image along the total spaces-étale augmentation is additive. -/
theorem pushforward_additive : (modulePushforward a).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (spacesEtaleAugmentationRinged U a)

/-- Total right-derived module direct image exists for the total spaces-étale augmentation. -/
theorem hasPushforward :
    RingedSite.ToposHom.NativeDerived.HasPushforward.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleAugmentationRinged U a) := by
  -- Local instance justification (defeq pin): the K-injective model must use the same native abelian structures as the displayed module homotopy localizations.
  letI := RingedSite.NativeDerived.abelian.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): normalize the target's addition before constructing its standard derived category and the comparison unit.
  letI := RingedSite.NativeDerived.abelian.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): retain the native standard localization on the source when applying the explicit K-injective universal witness.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (etaleTotalRingedSite U)
  -- Local instance justification (defeq pin): retain the native target localization in the actual K-injective functor and its augmentation comparison.
  letI := RingedSite.NativeDerived.hasDerivedCategory.{u} (spacesRingedSite X)
  -- Local instance justification (defeq pin): the explicit direct-image additive certificate uses the native addition pinned for this K-injective construction.
  letI := pushforward_additive a
  exact Functor.KInjectiveModel.Homotopy.hasRightDerived (modulePushforward a)

/-- Degreewise module direct image on homotopy categories for the total spaces-étale
augmentation. -/
def pushforwardHomotopy :
    RingedSite.Hom.ModuleHomotopy.{u} (etaleTotalRingedSite U) ⥤
      RingedSite.Hom.ModuleHomotopy.{u} (spacesRingedSite X) :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (modulePushforward a)
    (pushforward_additive a) (ComplexShape.up ℤ)

/-- The unbounded right-derived module direct image along the total spaces-étale
augmentation. -/
def pushforward :
    RingedSite.NativeDerived.category.{u} (etaleTotalRingedSite U) ⥤
      RingedSite.NativeDerived.category.{u} (spacesRingedSite X) :=
  @RingedSite.ToposHom.NativeDerived.pushforward _ _ _ _
    (spacesEtaleAugmentationRinged U a) _ _ (hasPushforward a)

/-- The canonical comparison from degreewise direct image to right-derived direct image
along the total spaces-étale augmentation. -/
def pushforwardUnit :
    pushforwardHomotopy a ⋙ RingedSite.NativeDerived.localization.{u} (spacesRingedSite X) ⟶
      RingedSite.NativeDerived.localization.{u} (etaleTotalRingedSite U) ⋙ pushforward a :=
  let L := RingedSite.NativeDerived.localization.{u} (etaleTotalRingedSite U)
  let W := RingedSite.NativeDerived.quasiIso.{u} (etaleTotalRingedSite U)
  @Functor.totalRightDerivedUnit _ _ _ _ _ _
    (RingedSite.ToposHom.NativeDerived.pushforwardToDerived (spacesEtaleAugmentationRinged U a)) L W
    (RingedSite.NativeDerived.localizationIsLocalization.{u} (etaleTotalRingedSite U)) (hasPushforward a)

/-- The unit of module pullback and direct image for the total spaces-étale augmentation. -/
def ordinaryUnit (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    F ⟶ (modulePushforward a).obj ((modulePullback a).obj F) :=
  (moduleAdjunction a).unit.app F

/-- The ordinary comparison is the component of the module-adjunction unit. -/
theorem ordinaryUnit_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    ordinaryUnit a F = (moduleAdjunction a).unit.app F := sorry

/-- Degreewise direct image commutes with placing a module in degree zero. -/
def pushforwardSingleIso (G : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) :
    (pushforwardHomotopy a).obj
        ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))
          0).obj G) ≅
      (HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (spacesRingedSite X)) 0).obj
        ((modulePushforward a).obj G) :=
  let hZero := @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
    (modulePushforward a) (pushforward_additive a)
  (@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _ (modulePushforward a)
      (pushforward_additive a) (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) ≪≫
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
        (modulePushforward a) hZero (ComplexShape.up ℤ) _ 0).app G)

/-- The canonical map from a module in degree zero to the right-derived direct image of its
pullback along the total spaces-étale augmentation. -/
def toPushforwardDerived (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X)).obj
        ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (spacesRingedSite X)) 0).obj F) ⟶
      (pushforward a).obj
        ((RingedSite.NativeDerived.localization.{u} (etaleTotalRingedSite U)).obj
          ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))
            0).obj ((modulePullback a).obj F))) :=
  (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X)).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (ordinaryUnit a F))) ≫
    (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X)).map
      (pushforwardSingleIso a ((modulePullback a).obj F)).inv ≫
    (pushforwardUnit a).app
      ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))
        0).obj ((modulePullback a).obj F))

/-- The derived comparison is the localized ordinary unit followed by the degree-zero
comparison and the total right-derived unit. -/
theorem toPushforwardDerived_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    toPushforwardDerived a F =
      (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X)).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (ordinaryUnit a F))) ≫
        (RingedSite.NativeDerived.localization.{u} (spacesRingedSite X)).map
          (pushforwardSingleIso a ((modulePullback a).obj F)).inv ≫
        (pushforwardUnit a).app
          ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))
            0).obj ((modulePullback a).obj F)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

end
