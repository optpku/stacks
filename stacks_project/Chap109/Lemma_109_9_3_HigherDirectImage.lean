/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.HigherDirectImage

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Y.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    higherDirectImageOne f =
      ModuleDerived.cohomologySheaf
        ((Modules.moduleDerivedPushforward f).obj (structureSheafDerived X)) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOneBaseChangeHom :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y),
    (Modules.pullback g).obj (higherDirectImageOne f) ⟶
      higherDirectImageOne (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOneBaseChangeHom_eq :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
    higherDirectImageOneBaseChangeHom f g =
      let OX := structureSheafDerived X
      let E := (Modules.moduleDerivedPushforward f).obj OX
      ModuleDerived.cohomologySheafPullbackComparison g E 1 ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
              (derivedPullbackPushforwardAdjunction (pullback.snd f g))
              (DerivedQCoh.cohomologyBaseChangeCartesianIso
                (IsPullback.of_hasPullback f g))).app OX) ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((Modules.moduleDerivedPushforward (pullback.snd f g)).map
            (ModuleDerived.structureSheafDerivedPullbackCounit (pullback.fst f g))))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
