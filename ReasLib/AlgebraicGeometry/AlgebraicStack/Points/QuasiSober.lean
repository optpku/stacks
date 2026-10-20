/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Quasi-sobriety of points of locally Noetherian algebraic stacks

The points space of a locally Noetherian algebraic stack is quasi-sober:
every irreducible closed subset has a generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian

/-- The points space of a locally Noetherian algebraic stack is quasi-sober. -/
theorem quasiSober {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @QuasiSober (Points X) τ :=
  sorry

/-- Every irreducible closed subset of the points space of a locally Noetherian
algebraic stack has a generic point. -/
theorem exists_isGenericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {T : Set (Points X)}
    (hT_irred : @IsIrreducible (Points X) τ T)
    (hT_closed : @IsClosed (Points X) τ T) :
    ∃ x, @IsGenericPoint (Points X) τ x T :=
  (quasiSober X τ hτ).sober hT_irred hT_closed

/-- The canonical point space of a locally Noetherian algebraic stack is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] : QuasiSober (Points X) :=
  quasiSober X (Points.topology X) (isPointsTopology_pointsTopology X)

end AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian
