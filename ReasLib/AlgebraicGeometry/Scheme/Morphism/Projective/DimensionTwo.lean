/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.DimensionTwo
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Projectivity of regular two-dimensional schemes

A proper morphism from a regular scheme of dimension two to a Noetherian scheme is projective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Projective

/-- A proper morphism from a regular scheme of topological Krull dimension two to a Noetherian
scheme is projective. -/
@[stacks 0C5P]
theorem instOfProperRegularDimensionTwo
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Scheme.Regular X]
    (h_dim : topologicalKrullDim X = 2) : Projective f := sorry

/-- Projectivity is inferred for proper morphisms from regular schemes of dimension two to
Noetherian schemes when the dimension equality is available as a fact. -/
instance instOfProperRegularDimensionTwoOfFact
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Scheme.Regular X]
    [Fact (topologicalKrullDim X = 2)] : Projective f :=
  instOfProperRegularDimensionTwo f Fact.out

end AlgebraicGeometry.Projective
