/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Closed points via residual gerbes

On a locally Noetherian algebraic stack, a point is closed if and only if its
residual-gerbe monomorphism is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (ClosedImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- A point of a locally Noetherian algebraic stack is closed if and only if
its residual-gerbe morphism is a closed immersion. -/
theorem mem_closedPoints_iff_closedImmersion {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian X] {x : Points X} (ι : Z ⟶ X) [IsResidualGerbe ι x] :
    x ∈ closedPoints (Points X) ↔ ClosedImmersion ι :=
  sorry

/-- If a residual-gerbe monomorphism is a closed immersion, then the marked
point is a closed point of the algebraic stack. -/
theorem mem_closedPoints {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] {x : Points X} (ι : Z ⟶ X)
    [IsResidualGerbe ι x] [ClosedImmersion ι] :
    x ∈ closedPoints (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
