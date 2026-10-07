module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap88.Remark_88_23_6_Pullback

/-!
# Completing the relative diagonal along a closed subset

The fibre product of completions of a morphism of algebraic spaces along a
closed subset is the completion of the fibre product, so the relative diagonal
of the completed morphism is the completion of the relative diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 88.23.6 (1): for a morphism `f : X' ⟶ X` of algebraic spaces over a
scheme `S` and a closed subset `T ⊆ Points X`, writing `T'` for the inverse
image of `T` on `X'` and `T''` for `completionAlong.fibreProductInverseImage f T`
on `X' ×_X X'`, the completed fibre product
`X'_/T' ×_{X_/T} X'_/T'` coincides with `(X' ×_X X')_/T''` as subfunctors of
`X' ×_X X'`. -/
@[stacks 0GDF]
theorem isPullback_completionAlong_fibreProduct {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    IsPullback (completionAlong.fibreProductFst f T) (completionAlong.fibreProductSnd f T)
      (completionAlong.map f T) (completionAlong.map f T) :=
  sorry

/-- Remark 88.23.6 (2): in the situation of Remark 88.23.6 (1), the relative
diagonal `Δ_{f_/T}` of `completionAlong.map f T` equals the completion
`(Δ_f)_/T''` of the relative diagonal of `f`. -/
@[stacks 0GDF]
theorem completionAlong_diagonal {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    completionAlong.diagonalMap f T ≫
        (isPullback_completionAlong_fibreProduct f T).isoPullback.hom =
      pullback.diagonal (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
