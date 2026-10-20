/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect

/-- Tensoring a perfect derived module by an invertible module concentrated in degree zero
preserves perfectness. -/
theorem tensorInvertible {X : Scheme.{u}}
    {E : ModuleDerived X.toRingedSpace}
    (hPerfect : ModuleDerived.IsPerfect E)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    ModuleDerived.IsPerfect
      (E ⊗ᴸ (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj L) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
