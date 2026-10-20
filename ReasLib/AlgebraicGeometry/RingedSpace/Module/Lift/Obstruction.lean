/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction.Opens
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Thickening
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealMul
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift
public import ReasLib.CategoryTheory.DerivedCategory.Ext

/-!
# Obstructions to lifting maps of modules along first-order thickenings

The connecting class of a map between reductions of modules transports under derived adjunction
to a canonical degree-one obstruction. Its vanishing is equivalent to existence of a lift.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback
  RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModuleMap

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- The connecting class of a map between reductions of modules, valued in the first Ext group
from the original source module to the pushforward of the target's ideal multiple. -/
def obstructionOver {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.singleFunctor X'.Modules 0).obj F',
      (DerivedCategory.singleFunctor X'.Modules 0).obj
        ((i _*).obj (idealMulRestrict i G'))) :=
  (DerivedCategory.singleFunctor X'.Modules 0).map
      ((pullbackPushforwardAdjunction i).homEquiv F' ((i^*).obj G') φ) ≫
    (ModuleExtension.ofPullback i G').shortExact.singleδ

/-- The ambient connecting class vanishes exactly when the map between reductions lifts to a
map between the original modules. -/
theorem obstructionOver_eq_zero_iff {F' G' : X'.Modules}
    (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstructionOver φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

/-- The canonical obstruction to lifting a map between reductions, valued in the first Ext
group from the derived pullback of the source module to the target's ideal multiple. -/
def obstruction {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    Ext⁽(1 : ℤ)⁾((L(i)^*).obj ((DerivedCategory.singleFunctor X'.Modules 0).obj F'),
      (DerivedCategory.singleFunctor X.Modules 0).obj (idealMulRestrict i G')) :=
  ((moduleDerivedAdjunctionOfOpens i).homEquiv _ _).symm
    (obstructionOver φ ≫
      (moduleDerivedPushforward.comparison i ((i _*).obj (idealMulRestrict i G'))
          (idealMulRestrict i G') (𝟙 _))⟦(1 : ℤ)⟧' ≫
        (ThickeningDerived.shiftIso i (1 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (idealMulRestrict i G')))

/-- The obstruction is the derived adjunct of the connecting class composed with the canonical
pushforward comparison and its degree-one shift comparison. -/
theorem obstruction_eq {F' G' : X'.Modules} (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstruction φ =
      ((moduleDerivedAdjunctionOfOpens i).homEquiv _ _).symm
        (obstructionOver φ ≫
          (moduleDerivedPushforward.comparison i ((i _*).obj (idealMulRestrict i G'))
              (idealMulRestrict i G') (𝟙 _))⟦(1 : ℤ)⟧' ≫
            (ThickeningDerived.shiftIso i (1 : ℤ)).inv.app
              ((DerivedCategory.singleFunctor X.Modules 0).obj
                (idealMulRestrict i G'))) := rfl

/-- A map between pullbacks of modules along a first-order thickening lifts to a map between
the original modules if and only if its canonical derived obstruction vanishes. -/
theorem obstruction_eq_zero_iff {F' G' : X'.Modules}
    (φ : (i^*).obj F' ⟶ (i^*).obj G') :
    obstruction φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end AlgebraicGeometry.RingedSpace.Hom.ModuleMap
