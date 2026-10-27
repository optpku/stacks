/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Unbounded derived pushforward from an open subspace

Direct image is evaluated on the specified K-injective replacement, then localized.
The adjunction maps descend the ordinary cochain adjunction and the actual augmentation.
Exact restriction supplies its native computation isomorphism. The inverse counit
uses the ordinary section-restriction inverse and the forward augmentation.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace ComplexShape
noncomputable section
universe u
namespace AlgebraicGeometry.RingedSpace
variable {X : RingedSpace.{u}}

/-- Total right derived direct image on the actual K-injective model. -/
@[stacks 08DP "derived open-pushforward owner"]
abbrev modulePushforwardFromOpenDerived (U : Opens X.carrier) :
    moduleDerivedOnOpen X U ⥤ ModuleDerived X :=
  Functor.KInjectiveModel.derived (modulePushforwardFromOpen U)

namespace OpenSubspace.Pushforward

/-- The ordinary adjunction applied degreewise. -/
def cochainAdjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ) ⊣
      (modulePushforwardFromOpen U).mapHomologicalComplex (up ℤ) :=
  Adjunction.mapHomologicalComplexAdjunction (adjunction X U) (up ℤ)

/-- The specified inverse ordinary counit, degree by degree. -/
def cochainCounitInv (X : RingedSpace.{u}) (U : Opens X.carrier)
    (B : CochainComplex (openSubspaceModuleCategory X U) ℤ) :
    B ⟶ ((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj
      (((modulePushforwardFromOpen U).mapHomologicalComplex (up ℤ)).obj B) where
  f n := (counitIso X U).inv.app (B.X n)
  comm' := by intros; sorry

/-- Localize the ordinary unit, then apply the actual K-injective augmentation. -/
def derivedUnitOnCochain (X : RingedSpace.{u}) (U : Opens X.carrier)
    (A : CochainComplex X.Modules ℤ) :
    DerivedCategory.Q.obj A ⟶
      (moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U).obj
        (DerivedCategory.Q.obj A) :=
  DerivedCategory.Q.map ((cochainAdjunction X U).unit.app A) ≫
    (Functor.KInjectiveModel.unit (modulePushforwardFromOpen U)).app
      ((moduleRestrictionComplexToOpen X U).obj A) ≫
    (modulePushforwardFromOpenDerived U).map
      (moduleRestrictionToOpenDerivedFactors X U A).inv

/-- Compute the model, apply the ordinary counit, and formally reverse augmentation. -/
def derivedCounitOnCochain (X : RingedSpace.{u}) (U : Opens X.carrier)
    (B : CochainComplex (openSubspaceModuleCategory X U) ℤ) :
    (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U).obj
      (DerivedCategory.Q.obj B) ⟶ DerivedCategory.Q.obj B :=
  (moduleRestrictionToOpenDerived X U).map
    ((Functor.KInjectiveModel.fac (modulePushforwardFromOpen U)).hom.app B) ≫
    (moduleRestrictionToOpenDerivedFactors X U
      (((modulePushforwardFromOpen U).mapHomologicalComplex (up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement
          (openSubspaceModuleCategory X U)).obj B))).hom ≫
    DerivedCategory.Q.map ((cochainAdjunction X U).counit.app
      ((CochainComplex.KInjectiveResolution.Construction.replacement
        (openSubspaceModuleCategory X U)).obj B)) ≫
    (Functor.KInjectiveModel.inputAugmentationIso B).inv

/-- Reverse the computation maps using forward augmentation and the section inverse. -/
def derivedCounitInvOnCochain (X : RingedSpace.{u}) (U : Opens X.carrier)
    (B : CochainComplex (openSubspaceModuleCategory X U) ℤ) :
    DerivedCategory.Q.obj B ⟶
      (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U).obj
        (DerivedCategory.Q.obj B) :=
  (Functor.KInjectiveModel.inputAugmentationIso B).hom ≫
    DerivedCategory.Q.map (cochainCounitInv X U
      ((CochainComplex.KInjectiveResolution.Construction.replacement
        (openSubspaceModuleCategory X U)).obj B)) ≫
    (moduleRestrictionToOpenDerivedFactors X U
      (((modulePushforwardFromOpen U).mapHomologicalComplex (up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement
          (openSubspaceModuleCategory X U)).obj B))).inv ≫
    (moduleRestrictionToOpenDerived X U).map
      ((Functor.KInjectiveModel.fac (modulePushforwardFromOpen U)).inv.app B)

/-- Naturality in every original cochain map. -/
theorem derivedUnitOnCochain_naturality (X : RingedSpace.{u}) (U : Opens X.carrier)
    {A B : CochainComplex X.Modules ℤ} (a : A ⟶ B) :
    DerivedCategory.Q.map a ≫ derivedUnitOnCochain X U B =
      derivedUnitOnCochain X U A ≫
        (moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U).map
          (DerivedCategory.Q.map a) := sorry

/-- Naturality of the specified counit. -/
theorem derivedCounitOnCochain_naturality (X : RingedSpace.{u}) (U : Opens X.carrier)
    {A B : CochainComplex (openSubspaceModuleCategory X U) ℤ} (a : A ⟶ B) :
    (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U).map
        (DerivedCategory.Q.map a) ≫ derivedCounitOnCochain X U B =
      derivedCounitOnCochain X U A ≫ DerivedCategory.Q.map a := sorry

/-- Naturality of the specified reverse counit. -/
theorem derivedCounitInvOnCochain_naturality (X : RingedSpace.{u}) (U : Opens X.carrier)
    {A B : CochainComplex (openSubspaceModuleCategory X U) ℤ} (a : A ⟶ B) :
    DerivedCategory.Q.map a ≫ derivedCounitInvOnCochain X U B =
      derivedCounitInvOnCochain X U A ≫
        (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U).map
          (DerivedCategory.Q.map a) := sorry

/-- Unit maps before localization descent. -/
def derivedUnitOnCochains (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Q ⋙ 𝟭 (ModuleDerived X) ⟶
      DerivedCategory.Q ⋙
        (moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U) where
  app A := derivedUnitOnCochain X U A
  naturality := fun _ _ a ↦ derivedUnitOnCochain_naturality X U a

/-- Counit maps before localization descent. -/
def derivedCounitOnCochains (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Q ⋙
        (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U) ⟶
      DerivedCategory.Q ⋙ 𝟭 (moduleDerivedOnOpen X U) where
  app B := derivedCounitOnCochain X U B
  naturality := fun _ _ a ↦ derivedCounitOnCochain_naturality X U a

/-- Reverse counit maps before localization descent. -/
def derivedCounitInvOnCochains (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory.Q ⋙ 𝟭 (moduleDerivedOnOpen X U) ⟶
      DerivedCategory.Q ⋙
        (modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U) where
  app B := derivedCounitInvOnCochain X U B
  naturality := fun _ _ a ↦ derivedCounitInvOnCochain_naturality X U a

/-- Native localization descends the supplied unit maps. -/
def restrictionDerivedUnit (X : RingedSpace.{u}) (U : Opens X.carrier) :
    𝟭 (ModuleDerived X) ⟶
      moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U :=
  Localization.liftNatTrans (DerivedCategory.Q (C := X.Modules))
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    _ _ _ _ (derivedUnitOnCochains X U)

/-- Native localization descends the supplied counit maps. -/
def derivedCounit (X : RingedSpace.{u}) (U : Opens X.carrier) :
    modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U ⟶
      𝟭 (moduleDerivedOnOpen X U) :=
  Localization.liftNatTrans (DerivedCategory.Q (C := openSubspaceModuleCategory X U))
    (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (up ℤ))
    _ _ _ _ (derivedCounitOnCochains X U)

/-- Native localization descends the supplied reverse maps. -/
def derivedCounitInv (X : RingedSpace.{u}) (U : Opens X.carrier) :
    𝟭 (moduleDerivedOnOpen X U) ⟶
      modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U :=
  Localization.liftNatTrans (DerivedCategory.Q (C := openSubspaceModuleCategory X U))
    (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (up ℤ))
    _ _ _ _ (derivedCounitInvOnCochains X U)

/-- First triangle law for the specified maps. -/
theorem derived_left_triangle (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.whiskerRight (restrictionDerivedUnit X U) (moduleRestrictionToOpenDerived X U) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (moduleRestrictionToOpenDerived X U) (derivedCounit X U) =
      NatTrans.id (𝟭 _ ⋙ moduleRestrictionToOpenDerived X U) := sorry

/-- Second triangle law for the specified maps. -/
theorem derived_right_triangle (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.whiskerLeft (modulePushforwardFromOpenDerived U) (restrictionDerivedUnit X U) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedCounit X U) (modulePushforwardFromOpenDerived U) =
      NatTrans.id (modulePushforwardFromOpenDerived U ⋙ 𝟭 _) := sorry

/-- The unbounded adjunction stores the displayed maps. -/
@[stacks 08DP "derived open restriction-pushforward adjunction"]
def derivedAdjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleRestrictionToOpenDerived X U ⊣ modulePushforwardFromOpenDerived U :=
  Adjunction.mkOfUnitCounit {
    unit := restrictionDerivedUnit X U
    counit := derivedCounit X U
    left_triangle := derived_left_triangle X U
    right_triangle := derived_right_triangle X U }

instance derivedIsLeftAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsLeftAdjoint (moduleRestrictionToOpenDerived X U) :=
  (derivedAdjunction X U).isLeftAdjoint

instance derivedIsRightAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsRightAdjoint (modulePushforwardFromOpenDerived U) :=
  (derivedAdjunction X U).isRightAdjoint

/-- The displayed reverse maps undo the counit. -/
theorem derivedCounit_hom_inv_id (X : RingedSpace.{u}) (U : Opens X.carrier) :
    derivedCounit X U ≫ derivedCounitInv X U = 𝟙 _ := sorry

/-- The counit undoes the displayed reverse maps. -/
theorem derivedCounit_inv_hom_id (X : RingedSpace.{u}) (U : Opens X.carrier) :
    derivedCounitInv X U ≫ derivedCounit X U = 𝟙 _ := sorry

/-- Both maps are specified before invertibility is asserted. -/
def derivedCounitIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    modulePushforwardFromOpenDerived U ⋙ moduleRestrictionToOpenDerived X U ≅
      𝟭 (moduleDerivedOnOpen X U) where
  hom := derivedCounit X U
  inv := derivedCounitInv X U
  hom_inv_id := derivedCounit_hom_inv_id X U
  inv_hom_id := derivedCounit_inv_hom_id X U

instance derivedCounitIsIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    IsIso (derivedAdjunction X U).counit := (derivedCounitIso X U).isIso_hom

@[stacks 08DP "derived open restriction-pushforward counit component"]
instance derivedCounitAppIsIso (X : RingedSpace.{u}) (U : Opens X.carrier)
    (F : moduleDerivedOnOpen X U) :
    IsIso ((derivedAdjunction X U).counit.app F) :=
  (derivedCounitIso X U).app F |>.isIso_hom

/-- Native fully faithful data use the constructed counit isomorphism. -/
@[stacks 08DP "derived open pushforward is fully faithful"]
def derivedFullyFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).FullyFaithful :=
  (derivedAdjunction X U).fullyFaithfulROfIsIsoCounit

instance derivedFull (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).Full := (derivedFullyFaithful X U).full

instance derivedFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpenDerived U).Faithful := (derivedFullyFaithful X U).faithful

end OpenSubspace.Pushforward
end AlgebraicGeometry.RingedSpace
