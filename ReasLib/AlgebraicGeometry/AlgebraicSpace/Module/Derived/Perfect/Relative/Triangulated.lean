/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative

/-! # Triangulated closure of relatively perfect derived modules on algebraic spaces -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The objects perfect relative to a flat, locally finitely presented morphism of
algebraic spaces form a triangulated object property. -/
instance perfectRelativeTo_isTriangulated (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty.IsTriangulated (perfectRelativeTo f) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
