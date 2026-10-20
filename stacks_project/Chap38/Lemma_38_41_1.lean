/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ModulePullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 38.41.1 (1): derived pullback of a perfect module sheaf of Tor dimension at most one
along a blowup agrees with ordinary pullback through the canonical comparison morphism. -/
@[stacks 0ESS] #check (AlgebraicGeometry.IsBlowup.singlePullbackComparison_isIso :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I]
    [DerivedCategory.DerivedTensor.Right.Has
      (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    IsIso (AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.singlePullbackComparison
      b.toShHom F 0))

/- Lemma 38.41.1 (2): ordinary pullback along the blowup remains perfect. -/
@[stacks 0ESS] #check (AlgebraicGeometry.IsBlowup.pullback_isPerfect :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I]
    [DerivedCategory.DerivedTensor.Right.Has
      (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    SheafOfModules.IsPerfect ((AlgebraicGeometry.Scheme.Modules.pullback b).obj F))

/- Lemma 38.41.1 (3): ordinary pullback along the blowup retains Tor dimension at most one. -/
@[stacks 0ESS] #check (AlgebraicGeometry.IsBlowup.pullback_hasTorDimensionLE_one :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.IsBlowup b I]
    [DerivedCategory.DerivedTensor.Right.Has
      (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has
      (C := AlgebraicGeometry.RingedSpace.Modules X'.toRingedSpace)] (F : X.Modules) (_ : SheafOfModules.IsPerfect F)
    (_ : AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE F 1),
    AlgebraicGeometry.RingedSpace.ModuleHasTorDimensionLE
      ((AlgebraicGeometry.Scheme.Modules.pullback b).obj F) 1)
