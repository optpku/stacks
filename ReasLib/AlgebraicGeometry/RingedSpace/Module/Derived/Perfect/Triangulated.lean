/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

@[expose] public section

/-!
# Triangulated closure of perfect derived modules on ringed spaces

This leaf specializes the bundled ringed-site triangulated API to the canonical opens site of a
ringed space.  Its public statements involve only the ringed space, a distinguished triangle, and
perfectness of its vertices.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Perfect objects of `D(𝒪_X)` form a triangulated object property. -/
@[stacks 08CR "triangulated closure"]
instance isPerfect_isTriangulated :
    ObjectProperty.IsTriangulated (perfect (X := X)) := sorry

/-- In a distinguished triangle, perfectness of the first two objects
implies perfectness of the third. -/
@[stacks 08CR "(1)"]
theorem isPerfect_obj₃_of_distinguished_triangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := sorry

/-- In a distinguished triangle, perfectness of the first and third objects
implies perfectness of the second. -/
@[stacks 08CR "(2)"]
theorem isPerfect_obj₂_of_distinguished_triangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₁ : IsPerfect T.obj₁) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₂ := sorry

/-- In a distinguished triangle, perfectness of the second and third objects
implies perfectness of the first. -/
@[stacks 08CR "(3)"]
theorem isPerfect_obj₁_of_distinguished_triangle
    (T : Triangle (ModuleDerived X)) (hT : T ∈ distTriang (ModuleDerived X))
    (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₁ := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
