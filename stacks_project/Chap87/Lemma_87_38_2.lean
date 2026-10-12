/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap87.Lemma_87_38_2_Completion

/-!
# Cartesianness of completion along a closed subspace

A morphism of algebraic spaces induces a cartesian square of completions along
a closed subspace and its inverse image, in the fppf functor-of-points
category. In particular the induced map of completions is representable by
algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.38.2 (1): For a morphism `f : X' ⟶ X` of algebraic spaces over a scheme
`S` and a closed subspace `Z ⊂ X` given by a closed immersion `i : Z ⟶ X`, writing
`Z' = f⁻¹(Z) = X' ×_X Z` for the inverse image `inverseImage f i` with inclusion
`inverseImageι f i`, the square
`completionAlongSubspace (inverseImageι f i) ⟶ X'.functorOfPoints` over
`completionAlongSubspace i ⟶ X.functorOfPoints` is cartesian in
`(Over S)ᵒᵖ ⥤ Type u`. -/
@[stacks 0GXV]
theorem completionAlongSubspace_isPullback {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    IsPullback (completionAlongSubspace.ι (inverseImageι f i))
      (completionAlongSubspace.map f i) f (completionAlongSubspace.ι i) :=
  sorry

/-- Lemma 87.38.2 (2): In the situation of Lemma 87.38.2 (1), the induced morphism
`completionAlongSubspace.map f i` is representable by algebraic spaces. -/
@[stacks 0GXV]
theorem representableByAlgebraicSpaces_completionAlongSubspace_map
    {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    representableByAlgebraicSpaces (completionAlongSubspace.map f i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
