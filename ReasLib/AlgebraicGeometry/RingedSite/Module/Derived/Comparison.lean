/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Hom

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

/-- The canonical comparison between direct image and degree-zero inclusion. -/
def pushforwardSingleIso {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : X.Hom Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    (F : X.ModuleCat.{z}) :
    ((modulePushforward.{z} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F) ≅
      (HomotopyCategory.singleFunctor Y.ModuleCat 0).obj
        ((modulePushforward.{z} f).obj F) :=
  ((modulePushforward.{z} f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ≪≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (modulePushforward.{z} f) (ComplexShape.up ℤ) 0).app F)

/-- The ordinary module comparison transported to the total right-derived direct image. -/
def ordinaryToRightDerived {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : X.Hom Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    (F : X.ModuleCat.{z}) (G : Y.ModuleCat.{z})
    (h : G ⟶ (modulePushforward.{z} f).obj F) :
    (moduleLocalization.{z} Y).obj ((HomotopyCategory.singleFunctor Y.ModuleCat 0).obj G) ⟶
      (modulePushforwardDerived.{z} f).obj
        ((moduleLocalization.{z} X).obj ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F)) :=
  (moduleLocalization.{z} Y).map
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h)) ≫
    (moduleLocalization.{z} Y).map (pushforwardSingleIso f F).inv ≫
      ((modulePushforwardToDerived.{z} f).totalRightDerivedUnit
        (moduleLocalization.{z} X) (ModuleQis.{z} X)).app
          ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F)

/-- The ordinary-to-derived comparison is the localized degree-zero map followed by the
total right-derived unit. -/
theorem ordinaryToRightDerived_eq
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f)
      (ModuleQis.{z} X)]
    (F : ModuleCat.{z} X) (G : ModuleCat.{z} Y)
    (h : G ⟶ (modulePushforward.{z} f).obj F) :
    ordinaryToRightDerived f F G h =
      (moduleLocalization.{z} Y).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h)) ≫
        (moduleLocalization.{z} Y).map (pushforwardSingleIso f F).inv ≫
          ((modulePushforwardToDerived.{z} f).totalRightDerivedUnit
            (moduleLocalization.{z} X) (ModuleQis.{z} X)).app
            ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F) :=
  rfl

end RingedSite.Hom
