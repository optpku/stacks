/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-! # Perfectness of invertible modules in degree zero -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-zero single complex of an invertible module is perfect. -/
theorem isPerfect_single_of_isInvertible (L : X.Modules) [isInvertibleObject L] :
    IsPerfect ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
