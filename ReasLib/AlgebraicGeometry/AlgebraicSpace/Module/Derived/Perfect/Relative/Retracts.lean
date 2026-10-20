/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative

/-! # Retracts of relatively perfect derived modules on algebraic spaces -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The objects perfect relative to a flat, locally finitely presented morphism of
algebraic spaces are stable under retracts. -/
instance perfectRelativeTo_isStableUnderRetracts (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty.IsStableUnderRetracts (perfectRelativeTo f) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
