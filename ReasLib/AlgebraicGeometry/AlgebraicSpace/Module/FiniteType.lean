/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic

/-!
# Finite-type modules on an algebraic space
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is of
finite type. -/
instance instIsFiniteTypeUnit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
