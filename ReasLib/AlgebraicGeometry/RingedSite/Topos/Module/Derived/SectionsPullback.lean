/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Identity
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} Y)]
variable [Fact (∀ a b : Hom.globalSectionsRing X, a * b = b * a)]
variable [Fact (∀ a b : Hom.globalSectionsRing Y, a * b = b * a)]
variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModulePushforwardDerived f] [HasModuleDerivedAdjunction f]
variable {R S : Type w} [CommRing R] [CommRing S]
variable (α : R →+* Hom.globalSectionsRing Y) (β : S →+* Hom.globalSectionsRing X)
variable (σ : R →+* S) (h : f.globalSectionsMap.hom.comp α = β.comp σ)

/-- Base-linear pullback on derived sections with ordinary module coefficients,
obtained by scalar-adjoint transposition of the ordinary-coefficient base comparison. -/
def baseSectionsPullbackToOrdinary (F : RingedSite.ModuleCat.{w} Y) :
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).obj
      ((Hom.moduleDerivedGlobalSections.{w} Y).obj
        ((Hom.moduleLocalization.{w} Y).obj
          ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} Y) (0 : ℤ)).obj F))) ⟶
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ).obj
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).obj
        ((Hom.moduleDerivedGlobalSections.{w} X).obj
          ((Hom.moduleLocalization.{w} X).obj
            ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X) (0 : ℤ)).obj
              (f.modulePullback.obj F))))) :=
  let ordinarySingleIso :
      (modulePullbackToDerived f).obj
        ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} Y) (0 : ℤ)).obj F) ≅
      (Hom.moduleLocalization.{w} X).obj
        ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X) (0 : ℤ)).obj
          (f.modulePullback.obj F)) :=
    (Hom.moduleLocalization.{w} X).mapIso
      ((HomotopyCategory.quotient _ (up ℤ)).mapIso
        ((@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
          f.modulePullback
          (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ f.modulePullback
            (modulePullback_additive f)) (up ℤ) inferInstance 0).app F))
  (CategoryTheory.ModuleCat.derivedExtensionRestrictionAdjunction σ).homEquiv _ _
    (f.baseScalarComparisonToOrdinary α β σ h F) ≫
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ).map
      ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).map
        ((Hom.moduleDerivedGlobalSections.{w} X).map ordinarySingleIso.hom))

variable (β₀ : R →+* Hom.globalSectionsRing X)
variable (h₀ : f.globalSectionsMap.hom.comp α = β₀.comp (RingHom.id R))

/-- Pullback on derived sections over one fixed base ring, with both ordinary
coefficient modules placed in degree zero. -/
def sameBaseSectionsPullback (F : RingedSite.ModuleCat.{w} Y) :
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).obj
      ((Hom.moduleDerivedGlobalSections.{w} Y).obj
        ((Hom.moduleLocalization.{w} Y).obj
          ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} Y) (0 : ℤ)).obj F))) ⟶
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars β₀).obj
      ((Hom.moduleDerivedGlobalSections.{w} X).obj
        ((Hom.moduleLocalization.{w} X).obj
          ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X) (0 : ℤ)).obj
            (f.modulePullback.obj F)))) :=
  f.baseSectionsPullbackToOrdinary α β₀ (RingHom.id R) h₀ F ≫
    CategoryTheory.ModuleCat.DerivedRestriction.idIso.hom.app _

/-- Same-base pullback on derived sections is natural in the ordinary coefficient module. -/
theorem sameBaseSectionsPullback_naturality
    {F G : RingedSite.ModuleCat.{w} Y} (φ : F ⟶ G) :
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).map
        ((Hom.moduleDerivedGlobalSections.{w} Y).map
          ((Hom.moduleLocalization.{w} Y).map
            ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} Y) (0 : ℤ)).map φ))) ≫
        f.sameBaseSectionsPullback α β₀ h₀ G =
      f.sameBaseSectionsPullback α β₀ h₀ F ≫
        (CategoryTheory.ModuleCat.derivedRestrictionOfScalars β₀).map
          ((Hom.moduleDerivedGlobalSections.{w} X).map
            ((Hom.moduleLocalization.{w} X).map
              ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X) (0 : ℤ)).map
                (f.modulePullback.map φ)))) := sorry

end RingedSite.ToposHom
