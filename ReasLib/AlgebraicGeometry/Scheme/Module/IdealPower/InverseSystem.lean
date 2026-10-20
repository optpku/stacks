/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Filtration
public import ReasLib.CategoryTheory.InverseSystem.Positive

/-!
# Positive inverse systems of ideal powers

This module packages the ideal-power filtration of a scheme module as a positive inverse
system and identifies its stages and transition maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.Modules.IdealPowerProduct

variable {X : Scheme.{v}}

/-- The identity law for the positive ideal-power module system. -/
theorem positiveSystem_map_id (I : X.IdealSheafData) (F : X.Modules)
    (n : OrderDual ℕ+) :
    (IdealPowerFiltration.filtration I F).inclusion
        (Int.ofNat_le.mpr (𝟙 n).le) =
      𝟙 (Subobject.underlying.obj ((IdealPowerFiltration.filtration I F).stage
        (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ))) := sorry

/-- The composition law for the positive ideal-power module system. -/
theorem positiveSystem_map_comp (I : X.IdealSheafData) (F : X.Modules)
    {i j k : OrderDual ℕ+} (f : i ⟶ j) (g : j ⟶ k) :
    (IdealPowerFiltration.filtration I F).inclusion
        (Int.ofNat_le.mpr (f ≫ g).le) =
      (IdealPowerFiltration.filtration I F).inclusion
          (Int.ofNat_le.mpr f.le) ≫
        (IdealPowerFiltration.filtration I F).inclusion
          (Int.ofNat_le.mpr g.le) := sorry

/-- The positive inverse system whose stage `n` is the module `I ^ n F`. -/
noncomputable def positiveSystem (I : X.IdealSheafData) (F : X.Modules) :
    PNatInverseSystem X.Modules where
  obj n := (IdealPowerFiltration.filtration I F).stage
    (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)
  map f := (IdealPowerFiltration.filtration I F).inclusion
    (Int.ofNat_le.mpr f.le)
  map_id n := positiveSystem_map_id I F n
  map_comp f g := positiveSystem_map_comp I F f g

/-- A stage of the positive ideal-power module system is the corresponding ideal-power
subobject. -/
theorem positiveSystem_stage (I : X.IdealSheafData) (F : X.Modules) (n : ℕ+) :
    (positiveSystem I F).stage n =
      (idealPowerProductSubobject I F n : X.Modules) := sorry

/-- Every transition of the positive ideal-power module system is the canonical filtration
inclusion. -/
theorem positiveSystem_transitionMap (I : X.IdealSheafData) (F : X.Modules)
    {m n : ℕ+} (h : m ≤ n) :
    OrderDualInverseSystem.transitionMap (positiveSystem I F) h =
      (IdealPowerFiltration.filtration I F).inclusion
        (Int.ofNat_le.mpr h) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealPowerProduct
