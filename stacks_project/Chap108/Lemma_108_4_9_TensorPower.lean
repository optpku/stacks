/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TensorPower

/-! # Integral tensor powers of derived modules -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.tensorPowerInt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, ModuleDerived X → ℤ → ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.tensorPowerFamily :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ},
    (Fin r → ModuleDerived X) → tensorPowerIndex r → ModuleDerived X)
