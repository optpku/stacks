/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Quasi-projectivity of regular two-dimensional schemes

A separated finite-type morphism from a regular scheme of dimension two to a Noetherian scheme
is quasi-projective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.QuasiProjective

/-- A separated finite-type morphism from a regular scheme of topological Krull dimension two
to a Noetherian scheme is quasi-projective. -/
@[stacks 0C5N]
theorem instOfRegularDimensionTwo
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (h_dim : topologicalKrullDim X = 2) : QuasiProjective f := sorry

/-- Quasi-projectivity is inferred for separated finite-type morphisms from regular schemes
of dimension two to Noetherian schemes when the dimension equality is available as a fact. -/
instance instOfRegularDimensionTwoOfFact
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    [Fact (topologicalKrullDim X = 2)] : QuasiProjective f :=
  instOfRegularDimensionTwo f Fact.out

end AlgebraicGeometry.QuasiProjective
