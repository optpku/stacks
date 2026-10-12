/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap107.Lemma_107_5_9_RelativeDimension

/-!
# Dimension formula for smooth morphisms of algebraic stacks

A smooth morphism of locally Noetherian algebraic stacks adds the
Definition 107.5.7 relative dimension at a point to the local dimension of
the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.10: if `f : U ⟶ X` is a smooth morphism of locally Noetherian
algebraic stacks, and if `u ∈ |U|` has image `x ∈ |X|`, then
`dimensionAt u = dimensionAt x + relativeDimensionAt f u`, where
`relativeDimensionAt` is the relative dimension of Definition 107.5.7. -/
@[stacks 0DRP]
theorem dimensionAt_eq_image_add_relativeDimensionAt {S : Scheme.{u}}
    {U X : GroupoidsOver S} [AlgebraicStack U] [AlgebraicStack X]
    [IsLocallyNoetherian U] [IsLocallyNoetherian X] (f : U ⟶ X)
    [Smooth f] [LocallyOfFiniteType f] (u : Points U) :
    dimensionAt u = dimensionAt (Points.map f u) + relativeDimensionAt f u :=
  sorry

end AlgebraicGeometry.AlgebraicStack
