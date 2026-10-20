module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Pullback

/-!
# Pullback of module sheaves along blowups

For perfect module sheaves of Tor dimension at most one, pullback along a blowup agrees
with derived pullback and preserves both perfectness and the Tor-dimension bound.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- For a perfect module sheaf of Tor dimension at most one, derived pullback along a blowup
agrees with ordinary pullback through the canonical comparison morphism. -/
theorem singlePullbackComparison_isIso {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (F : X.Modules) (hPerfect : SheafOfModules.IsPerfect F)
    (hTor : RingedSpace.ModuleHasTorDimensionLE F 1) :
    IsIso (RingedSpace.ModuleDerived.Cohomology.singlePullbackComparison b.toShHom F 0) := sorry

/-- Ordinary pullback along a blowup preserves perfect module sheaves of Tor dimension at
most one. -/
theorem pullback_isPerfect {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (F : X.Modules) (hPerfect : SheafOfModules.IsPerfect F)
    (hTor : RingedSpace.ModuleHasTorDimensionLE F 1) :
    SheafOfModules.IsPerfect ((Scheme.Modules.pullback b).obj F) := sorry

/-- Ordinary pullback along a blowup preserves Tor dimension at most one for perfect module
sheaves with that Tor-dimension bound. -/
theorem pullback_hasTorDimensionLE_one {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X'.toRingedSpace)]
    (F : X.Modules) (hPerfect : SheafOfModules.IsPerfect F)
    (hTor : RingedSpace.ModuleHasTorDimensionLE F 1) :
    RingedSpace.ModuleHasTorDimensionLE ((Scheme.Modules.pullback b).obj F) 1 := sorry

end AlgebraicGeometry.IsBlowup
