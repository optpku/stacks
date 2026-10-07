module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap87.Lemma_87_14_4_Completion

/-!
# Cartesianness of completion along a closed subset

A morphism of algebraic spaces induces a cartesian square of completions along a
closed subset and its preimage, in the fppf functor-of-points category. In
particular the induced map of completions is representable by algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.14.4 (1): For a morphism `f : X' ⟶ X` of algebraic spaces over a scheme
`S` and a closed subset `T ⊆ Points X`, writing `T'` for
`T.preimage (Points.continuous_map f)`, the square
`completionAlong X' T' ⟶ X'.functorOfPoints` over
`completionAlong X T ⟶ X.functorOfPoints` is cartesian in
`(Over S)ᵒᵖ ⥤ Type u`. -/
@[stacks 0APV]
theorem completionAlong_isPullback {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    IsPullback (completionAlong.ι X' (T.preimage (Points.continuous_map f)))
      (completionAlong.map f T) f (completionAlong.ι X T) :=
  sorry

/-- Lemma 87.14.4 (2): In the situation of Lemma 87.14.4 (1), the induced morphism
`completionAlong.map f T` is representable by algebraic spaces. -/
@[stacks 0APV]
theorem representableByAlgebraicSpaces_completionAlong_map
    {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    representableByAlgebraicSpaces (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
