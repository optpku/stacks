/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.IrreducibleComponent

/-!
# Dimension and irreducible components of algebraic stacks

The dimension at a point equals the supremum of the dimensions of the reduced
induced irreducible components passing through that point. In particular, it is
bounded above by that supremum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The dimension of a locally Noetherian algebraic stack at a point is at most
the supremum of the dimensions of its reduced induced components through that point. -/
theorem dimensionAt_le_iSup_irreducibleComponents_through
    {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    dimensionAt x ≤
      ⨆ T : { T : @irreducibleComponents (Points X) τ // x ∈ (T : Set (Points X)) },
        dimensionAt (irreducibleComponentSubstack.point hτ T.1 x T.2) :=
  sorry

/-- The dimension of a locally Noetherian algebraic stack at a point equals
the supremum of the dimensions of its reduced induced irreducible components
through that point. -/
theorem dimensionAt_eq_iSup_irreducibleComponents_through
    {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    dimensionAt x =
      ⨆ T : { T : @irreducibleComponents (Points X) τ // x ∈ (T : Set (Points X)) },
        dimensionAt (irreducibleComponentSubstack.point hτ T.1 x T.2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
