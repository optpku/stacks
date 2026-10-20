/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveVariety

/-- A morphism of projective varieties over an algebraically closed field with
finite fibers over all closed points is finite. -/
@[stacks 0EG7]
theorem isFinite_of_finite_closedPoint_fibers {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    (f : X ⟶ Y) (hfib : ∀ y ∈ closedPoints Y.left, (f.left ⁻¹' {y}).Finite) :
    IsFinite f.left := sorry

end AlgebraicGeometry.ProjectiveVariety
