/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Correspondence.GraphEvaluation

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 45.3.9
Let `f : Y ⟶ X` be a morphism of smooth projective schemes over `k`. Assume `X` and `Y`
equidimensional of dimensions `d` and `e`. Denote `a = [Γ_f] ∈ Corr^0(X, Y)` and
`aᵗ = [Γ_fᵗ] ∈ Corr^{d-e}(Y, X)`. Set `η_X = [Γ_{X ⟶ X ⨯ X}] ∈ Corr^0(X ⨯ X, X)`,
`η_Y = [Γ_{Y ⟶ Y ⨯ Y}] ∈ Corr^0(Y ⨯ Y, Y)`, `[X] ∈ Corr^{-d}(X, Spec(k))`, and
`[Y] ∈ Corr^{-e}(Y, Spec(k))`. The diagram with `a ⊗ id`, `id ⊗ aᵗ`, `η_X`, `η_Y`,
`[X]`, and `[Y]` is commutative in the category of correspondences. -/
@[stacks 0FG8]
#check (AlgebraicGeometry.Correspondence.graphTranspose_commutes :
  ∀ {k : Type u} [Field k] (X Y : AlgebraicGeometry.Correspondence.Category k)
    [EquidimensionalSpace X.scheme.left] [EquidimensionalSpace Y.scheme.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.scheme.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.scheme.left = (e : WithBot ℕ∞))
    (f : Y.scheme ⟶ X.scheme),
    let a := AlgebraicGeometry.Correspondence.rationalGraph f
    let aT := AlgebraicGeometry.Correspondence.transpose X.scheme Y.scheme d e hXdim hYdim 0 a
    AlgebraicGeometry.Correspondence.castDegree
        (AlgebraicGeometry.Correspondence.graphTranspose_upperDegree e)
        (AlgebraicGeometry.Correspondence.composition
          (AlgebraicGeometry.Correspondence.Category.product X Y).scheme Y.scheme
          (AlgebraicGeometry.SchemeOverField.point k)
          ((0 + 0 : ℤ) + 0) (-(e : ℤ))
          (AlgebraicGeometry.Correspondence.composition
            (AlgebraicGeometry.Correspondence.Category.product X Y).scheme
            (AlgebraicGeometry.Correspondence.Category.product Y Y).scheme Y.scheme
            (0 + 0) 0
            (AlgebraicGeometry.Correspondence.tensor a
              (AlgebraicGeometry.Correspondence.correspondenceId Y))
            (AlgebraicGeometry.Correspondence.graphOfDiagonal Y))
          (AlgebraicGeometry.Correspondence.fundamental Y e)) =
      AlgebraicGeometry.Correspondence.castDegree
        (AlgebraicGeometry.Correspondence.graphTranspose_lowerDegree d e)
        (AlgebraicGeometry.Correspondence.composition
          (AlgebraicGeometry.Correspondence.Category.product X Y).scheme X.scheme
          (AlgebraicGeometry.SchemeOverField.point k)
          ((0 + ((d : ℤ) - (e : ℤ) + 0)) + 0) (-(d : ℤ))
          (AlgebraicGeometry.Correspondence.composition
            (AlgebraicGeometry.Correspondence.Category.product X Y).scheme
            (AlgebraicGeometry.Correspondence.Category.product X X).scheme X.scheme
            (0 + ((d : ℤ) - (e : ℤ) + 0)) 0
            (AlgebraicGeometry.Correspondence.tensor
              (AlgebraicGeometry.Correspondence.correspondenceId X) aT)
            (AlgebraicGeometry.Correspondence.graphOfDiagonal X))
          (AlgebraicGeometry.Correspondence.fundamental X d)))
