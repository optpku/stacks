/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.IrreducibleComponents
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- 107.5.19.1: For a locally Noetherian algebraic stack, the dimension at a point
is at most the supremum of the dimensions of the induced reduced irreducible
components passing through that point. -/
@[stacks 0DS0] #check
  (AlgebraicGeometry.AlgebraicStack.dimensionAt_le_iSup_irreducibleComponents_through :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
      {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ),
      dimensionAt x ≤
        ⨆ T : { T : @irreducibleComponents (Points X) τ // x ∈ (T : Set (Points X)) },
          dimensionAt (irreducibleComponentSubstack.point hτ T.1 x T.2))

end AlgebraicGeometry.AlgebraicStack
