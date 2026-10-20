/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Retrocompactness of bounded fibre-dimension loci

For a locally finitely presented morphism of algebraic spaces, the locus of
points at which the relative dimension is at most a given natural number is
retrocompact in the canonical topology on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a locally finitely presented morphism of algebraic spaces, the locus
where the relative dimension is at most `n` is retrocompact in the canonical
topology on source points. -/
@[stacks 04NU]
theorem isRetrocompact_fiberDimensionLELocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (n : ℕ) {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    @IsRetrocompact (Points X) τ (fiberDimensionLELocus f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
