/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.SectionsComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived global-sections comparison

This file packages the module-valued form of the global-sections/direct-image comparison.  The
ordinary naturality map is transported to homotopy categories and then to total right-derived
functors; the target remains the derived category of modules over the global-sections ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

namespace ModuleSections

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}]
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [UnivLE.{uX, z}] [UnivLE.{uY, z}]

variable [Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToModuleDerived.{z} X) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToModuleDerived.{z} Y) (ModuleQis.{z} Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]

/-- The homotopy-level source functor for the derived global-sections comparison. -/
noncomputable abbrev derivedGlobalSectionsSource :
    ModuleHomotopy.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  moduleGlobalSectionsToModuleDerived.{z} X ⋙
    globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f

/-- The homotopy-level target functor for the derived global-sections comparison. -/
noncomputable abbrev derivedGlobalSectionsTarget :
    ModuleHomotopy.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  f.modulePushforward.{z}.mapHomotopyCategory (up ℤ) ⋙
    moduleGlobalSectionsToModuleDerived.{z} Y

/-- The source derived functor after restricting scalars along the global-sections map. -/
noncomputable abbrev derivedGlobalSectionsSourceDerived :
    ModuleDerived.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  moduleDerivedGlobalSections.{z} X ⋙
    globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f

/-- The derived direct-image functor followed by derived global sections. -/
noncomputable abbrev derivedGlobalSectionsTargetDerived :
    ModuleDerived.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  modulePushforwardDerived.{z} f ⋙ moduleDerivedGlobalSections.{z} Y

/-- The unit exhibiting `derivedGlobalSectionsSourceDerived` as a right-derived model of the
source homotopy functor. -/
noncomputable def derivedGlobalSectionsSourceUnit :
    derivedGlobalSectionsSource f ⟶
      moduleLocalization.{z} X ⋙ derivedGlobalSectionsSourceDerived f :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{z} X)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (moduleDerivedGlobalSections.{z} X)
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f)).hom

/-- The unit exhibiting `derivedGlobalSectionsTargetDerived` as a right-derived model of the
target homotopy functor. -/
noncomputable def derivedGlobalSectionsTargetUnit :
    derivedGlobalSectionsTarget f ⟶
      moduleLocalization.{z} X ⋙ derivedGlobalSectionsTargetDerived f :=
  Functor.whiskerLeft
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{z} Y)
        (moduleLocalization.{z} Y) (ModuleQis.{z} Y)) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{z} Y)
      (moduleDerivedGlobalSections.{z} Y)).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{z} f)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (moduleDerivedGlobalSections.{z} Y) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (modulePushforwardDerived.{z} f)
      (moduleDerivedGlobalSections.{z} Y)).hom

/- The derived units below are canonical right-derived models; their universal-property proofs are
deferred at the statement stage. -/

/-- The source unit is a right-derived-functor structure for scalar-restricted global sections. -/
@[stacks 0D6H "derived global-sections source model"]
noncomputable instance derivedGlobalSectionsSource_isRightDerived :
    (derivedGlobalSectionsSourceDerived f).IsRightDerivedFunctor
      (derivedGlobalSectionsSourceUnit f) (ModuleQis.{z} X) := sorry

/-- The target unit is a right-derived-functor structure for direct image followed by global
sections. -/
@[stacks 0D6H "derived global-sections target model"]
noncomputable instance derivedGlobalSectionsTarget_isRightDerived :
    (derivedGlobalSectionsTargetDerived f).IsRightDerivedFunctor
      (derivedGlobalSectionsTargetUnit f) (ModuleQis.{z} X) := sorry

/-- The homotopy-level natural transformation underlying the derived global-sections comparison. -/
@[stacks 0D6H "derived module global-sections naturality"]
noncomputable def derivedGlobalSectionsPushforwardNat :
    derivedGlobalSectionsSource f ⟶ derivedGlobalSectionsTarget f :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing X)) (up ℤ) ⥤
          ModuleSections.Derived.{z} X)
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f)).hom ≫
    Functor.whiskerLeft
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).mapDerivedCategoryFactorsh.hom) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y)).inv ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (moduleGlobalSectionsFunctor.{z} X ⋙
            (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
              _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
                _root_.ModuleCat.{z} (globalSectionsRing Y)))) (up ℤ)).hom)
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (moduleGlobalSectionsPushforwardNatIso.{z} f).hom (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y)) (up ℤ)).inv)
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsFunctor.{z} Y).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y)).hom

/- The derived comparison is obtained from the universal property of the two right-derived
functors.  Keeping this construction in the library makes the comparison reusable without
reconstructing the localization square in each chapter. -/

/-- The canonical derived global-sections/direct-image comparison. -/
@[stacks 0D6H "derived global-sections comparison"]
noncomputable def derivedGlobalSectionsPushforwardComparison :
    derivedGlobalSectionsSourceDerived f ⟶ derivedGlobalSectionsTargetDerived f :=
  Functor.rightDerivedNatTrans
    (derivedGlobalSectionsSourceDerived f)
    (derivedGlobalSectionsTargetDerived f)
    (derivedGlobalSectionsSourceUnit f)
    (derivedGlobalSectionsTargetUnit f)
    (ModuleQis.{z} X)
    (derivedGlobalSectionsPushforwardNat f)

/-- The derived global-sections/direct-image comparison is an isomorphism. -/
@[stacks 0D6H "derived global-sections comparison isomorphism"]
noncomputable instance derivedGlobalSectionsPushforwardComparison_isIso :
    IsIso (derivedGlobalSectionsPushforwardComparison f) := sorry

/-- The derived comparison as a reusable natural isomorphism. -/
@[stacks 0D6H "derived global-sections comparison isomorphism"]
noncomputable def derivedGlobalSectionsPushforwardIso :
    derivedGlobalSectionsSourceDerived f ≅ derivedGlobalSectionsTargetDerived f :=
  asIso (derivedGlobalSectionsPushforwardComparison f)

/-- Each object component of the derived global-sections comparison is invertible. -/
@[stacks 0D6H "derived global-sections comparison component"]
theorem derivedGlobalSectionsPushforwardComparison_app_isIso
    (K : ModuleDerived.{z} X) :
    IsIso ((derivedGlobalSectionsPushforwardComparison f).app K) := sorry

end ModuleSections

end RingedSite.Hom
