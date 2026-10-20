/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomotopyCategory

/-- The homotopy category of integer-indexed cochain complexes in an additive category
is triangulated. -/
instance isTriangulated (A : Type u) [Category.{v} A] [Preadditive A]
    [HasBinaryBiproducts A] [HasZeroObject A] :
    CategoryTheory.IsTriangulated (HomotopyCategory A (ComplexShape.up ℤ)) := inferInstance

end HomotopyCategory
