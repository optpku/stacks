/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ConnectedComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber

/-!
# Component counts of locally quasi-finite fibres

This file records the equality and finite boundedness of geometric fibre-component
counts for locally finite-type, locally quasi-finite morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/-- For a locally finite-type, locally quasi-finite morphism, the geometric
irreducible- and connected-component count functions agree. -/
theorem geometricComponentCounts_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    f.geometricIrreducibleFiberComponentCount = f.geometricFiberComponentCount := sorry

/-- A locally finite-type, locally quasi-finite morphism with quasi-compact source has a
finite uniform upper bound for its geometric fibre-component count. -/
theorem exists_geometricFiberComponentCount_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] :
    ∃ d : ℕ, ∀ y : Y, f.geometricFiberComponentCount y ≤ d := sorry

/-- If the target is inhabited, the geometric fibre-component count of a locally finite-type,
locally quasi-finite morphism with quasi-compact source attains a finite maximum. -/
theorem exists_isGreatest_geometricFiberComponentCount
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] [Nonempty Y] :
    ∃ d : ℕ, IsGreatest (Set.range f.geometricFiberComponentCount) d := sorry

end AlgebraicGeometry.LocallyQuasiFinite
