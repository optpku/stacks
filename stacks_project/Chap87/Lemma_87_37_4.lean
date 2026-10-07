module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap87.Lemma_87_37_4_Completion

/-!
# Cartesianness of recompletion along a closed subset

A morphism of formal algebraic spaces induces a cartesian square of completions
along a closed subset of the reduction and its preimage.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.37.4: For a morphism `f : X' ⟶ X` of formal algebraic spaces over a
scheme `S` and a closed subset `T ⊆ Points (reduction X)`, writing `T'` for
`T.preimage (Points.continuous_map (mapReduction f))`, the square
`completionAlong X' T' ⟶ X'` over `completionAlong X T ⟶ X` is cartesian in
formal algebraic spaces over `S`. -/
@[stacks 0GVT]
theorem completionAlong_isPullback {S : Scheme.{u}} {X' X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X'] [IsFormalAlgebraicSpace X]
    [Reduction X'] [Reduction X] (f : X' ⟶ X)
    (T : Closeds (Points (reduction X))) :
    IsPullback
      (completionAlong.ι X' (T.preimage (Points.continuous_map (mapReduction f))))
      (completionAlong.map f T) f (completionAlong.ι X T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
