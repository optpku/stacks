module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Hom

noncomputable section

universe u

namespace RingedSite.Hom

/-- The canonical comparison between direct image and degree-zero inclusion. -/
def pushforwardSingleIso {X Y : RingedSite.{u+1,u,u}} (f : X.Hom Y)
    (F : X.ModuleCat.{u+1}) :
    ((modulePushforward.{u+1} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F) ≅
      (HomotopyCategory.singleFunctor Y.ModuleCat 0).obj
        ((modulePushforward.{u+1} f).obj F) :=
  ((modulePushforward.{u+1} f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ≪≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (modulePushforward.{u+1} f) (ComplexShape.up ℤ) 0).app F)

/-- The ordinary module comparison transported to the total right-derived direct image. -/
def ordinaryToRightDerived {X Y : RingedSite.{u+1,u,u}} (f : X.Hom Y)
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{u+1} f) (ModuleQis.{u+1} X)]
    (F : X.ModuleCat.{u+1}) (G : Y.ModuleCat.{u+1})
    (h : G ⟶ (modulePushforward.{u+1} f).obj F) :
    (moduleLocalization.{u+1} Y).obj ((HomotopyCategory.singleFunctor Y.ModuleCat 0).obj G) ⟶
      (modulePushforwardDerived.{u+1} f).obj
        ((moduleLocalization.{u+1} X).obj ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F)) :=
  (moduleLocalization.{u+1} Y).map
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map h)) ≫
    (moduleLocalization.{u+1} Y).map (pushforwardSingleIso f F).inv ≫
      ((modulePushforwardToDerived.{u+1} f).totalRightDerivedUnit
        (moduleLocalization.{u+1} X) (ModuleQis.{u+1} X)).app
          ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F)

end RingedSite.Hom
