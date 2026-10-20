/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Geometric connectedness under field extension

This file records invariance of geometric connectedness under extension of the
ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GeometricallyConnected.BaseChange

/-- Geometric connectedness is invariant under base change along a field extension. -/
theorem iff_fieldExtension
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    {K : Type u} [Field K] [Algebra k K] :
    GeometricallyConnected f ↔
      GeometricallyConnected (FieldExtension.toBase k K f) := sorry

end AlgebraicGeometry.GeometricallyConnected.BaseChange
