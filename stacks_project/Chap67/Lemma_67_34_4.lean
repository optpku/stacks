/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Locus

/-!
# Openness of bounded fibre-dimension loci

For a locally finite-type morphism of algebraic spaces, the locus of points
at which the relative dimension is at most a given natural number is open in
the canonical topology on points.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 67.34.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `n : ℕ`. Assume `f` is locally of finite type.
The set `W_n` of points of `Points X` at which the relative dimension of `f`
is at most `n` is open in the canonical topology on `Points X`. -/
@[stacks 04NT]
#check (AlgebraicGeometry.AlgebraicSpace.isOpen_fiberDimensionLELocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (n : ℕ)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ),
    @IsOpen (Points X) τ (fiberDimensionLELocus f n))
