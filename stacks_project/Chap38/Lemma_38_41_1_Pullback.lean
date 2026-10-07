module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ModulePullback

/-!
# Compatibility checks for pullback along blowups

This module keeps the former chapter import path available while the mathematical declarations
live in their reusable owner.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.IsBlowup.singlePullbackComparison_isIso :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    IsIso (AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.singlePullbackComparison
      b.toShHom F 0))

#check (AlgebraicGeometry.IsBlowup.pullback_isPerfect :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    SheafOfModules.IsPerfect ((AlgebraicGeometry.Scheme.Modules.pullback b).obj F))

#check (AlgebraicGeometry.IsBlowup.pullback_hasTorDimensionLE_one :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
      ((AlgebraicGeometry.Scheme.Modules.pullback b).obj F) 1)
