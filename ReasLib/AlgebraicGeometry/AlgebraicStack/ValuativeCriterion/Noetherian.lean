/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare.ClosedPoint

/-!
# Noetherian valuative existence for algebraic stacks

A finite-type morphism to a locally Noetherian stack admits a discrete
valuation ring square reaching any point in the closure of its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a finite-type morphism of algebraic stacks with locally Noetherian target,
every point in the closure of the image is the image of the closed point in a
valuative square whose valuation ring is a discrete valuation ring and whose
generic arrow comes from its field of fractions. -/
@[stacks 0H2B]
theorem exists_dvrValuativeCommSq_of_mem_closure_range
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    {y : Points Y}
    (hy : y ∈ closure (Set.range (Points.map f))) :
    ∃ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R ∧ sq.closedPointImage = y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
