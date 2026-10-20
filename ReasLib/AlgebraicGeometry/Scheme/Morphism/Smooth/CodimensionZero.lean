/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic

/-!
# Smoothness in codimension zero

This module defines smoothness at the generic points of every fibre of a scheme morphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism is smooth in codimension zero when it is smooth at every generic point
of every fibre. -/
def smoothInCodimensionZero {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (x : f.fiber s),
    x ∈ genericPoints (f.fiber s) → f.SmoothAt ((f.fiberι s) x)

namespace smoothInCodimensionZero

/-- Smoothness in codimension zero gives smoothness at a generic point of a chosen fibre. -/
theorem smoothAt {X S : Scheme.{u}} {f : X ⟶ S}
    (h : f.smoothInCodimensionZero) (s : S) (x : f.fiber s)
    (hx : x ∈ genericPoints (f.fiber s)) :
    f.SmoothAt ((f.fiberι s) x) := sorry

/-- A smooth scheme morphism is smooth in codimension zero. -/
theorem of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    f.smoothInCodimensionZero := sorry

end smoothInCodimensionZero

end AlgebraicGeometry.Scheme.Hom
