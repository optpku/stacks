/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.InverseSystem

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.Modules.IdealPowerProduct

variable {X : Scheme.{v}}

#check (positiveSystem_map_id :
  ∀ (I : X.IdealSheafData) (F : X.Modules) (n : OrderDual ℕ+),
    (IdealPowerFiltration.filtration I F).inclusion
        (Int.ofNat_le.mpr (𝟙 n).le) =
      𝟙 (Subobject.underlying.obj ((IdealPowerFiltration.filtration I F).stage
        (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ))))

#check (positiveSystem_map_comp :
  ∀ (I : X.IdealSheafData) (F : X.Modules) {i j k : OrderDual ℕ+}
    (f : i ⟶ j) (g : j ⟶ k),
    (IdealPowerFiltration.filtration I F).inclusion
        (Int.ofNat_le.mpr (f ≫ g).le) =
      (IdealPowerFiltration.filtration I F).inclusion
          (Int.ofNat_le.mpr f.le) ≫
        (IdealPowerFiltration.filtration I F).inclusion
          (Int.ofNat_le.mpr g.le))

#check (positiveSystem :
  X.IdealSheafData → X.Modules → PNatInverseSystem X.Modules)

#check (positiveSystem_stage :
  ∀ (I : X.IdealSheafData) (F : X.Modules) (n : ℕ+),
    (positiveSystem I F).stage n =
      (idealPowerProductSubobject I F n : X.Modules))

#check (positiveSystem_transitionMap :
  ∀ (I : X.IdealSheafData) (F : X.Modules) {m n : ℕ+} (h : m ≤ n),
    OrderDualInverseSystem.transitionMap (positiveSystem I F) h =
      (IdealPowerFiltration.filtration I F).inclusion (Int.ofNat_le.mpr h))

end AlgebraicGeometry.Scheme.Modules.IdealPowerProduct
