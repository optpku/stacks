/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_34_4_FiberDimensionLocus
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

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

/-- Lemma 67.34.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `n : ℕ`. Assume `f` is locally of finite
presentation. The set `W_n` of Lemma 67.34.4, consisting of the points of
`Points X` at which the relative dimension of `f` is at most `n`, is
retrocompact in the canonical topology on `Points X`. -/
@[stacks 04NU]
theorem isRetrocompact_fiberDimensionLELocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (n : ℕ) {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    @IsRetrocompact (Points X) τ (fiberDimensionLELocus f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
