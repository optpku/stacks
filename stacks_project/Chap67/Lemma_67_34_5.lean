/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.FinitePresentation
import StacksCheckRecall

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

/- Lemma 67.34.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `n : ℕ`. Assume `f` is locally of finite
presentation. The set `W_n` of Lemma 67.34.4, consisting of the points of
`Points X` at which the relative dimension of `f` is at most `n`, is
retrocompact in the canonical topology on `Points X`. -/
@[stacks 04NU] #check
  (AlgebraicGeometry.AlgebraicSpace.isRetrocompact_fiberDimensionLELocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] (n : ℕ) {τ : TopologicalSpace (Points X)}
      (hτ : IsPointsTopology X τ),
      @IsRetrocompact (Points X) τ (fiberDimensionLELocus f n))

end AlgebraicGeometry.AlgebraicSpace
