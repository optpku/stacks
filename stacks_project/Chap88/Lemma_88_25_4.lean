/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Uniqueness of morphisms after checking the open complement and the completion

A morphism of locally Noetherian algebraic spaces is uniquely determined by its
restriction to the open complement of a closed subset and its map on the
completion along that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Lemma 88.25.4: Let `S` be a scheme. Let `X`, `W` be algebraic spaces over
`S` with `X` locally Noetherian. Let `T ⊂ Points X` be closed. Let `a, b : X ⟶ W`
be morphisms of algebraic spaces over `S` such that `a|_{X \ T} = b|_{X \ T}`
and such that `a_/T = b_/T` as morphisms `X_/T ⟶ W`. Then `a = b`.

Here `a|_{X \ T}` is `openComplementι X T ≫ a : openComplementAlong X T ⟶ W`,
and `a_/T` is `ι X T ≫ a : completionAlong X T ⟶ W.functorOfPoints`. -/
@[stacks 0GI1]
theorem eq_of_restrict_eq {S : Scheme.{u}} {X W : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {a b : X ⟶ W}
    (h_open : openComplementι X T ≫ a = openComplementι X T ≫ b)
    (h_completion : ι X T ≫ a = ι X T ≫ b) :
    a = b :=
  sorry

/-- Morphisms of algebraic spaces out of a locally Noetherian source are equal
if and only if they agree on the open complement of `T` and after completion
along `T`. -/
theorem eq_iff_restrict_eq {S : Scheme.{u}} {X W : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {a b : X ⟶ W} :
    a = b ↔
      openComplementι X T ≫ a = openComplementι X T ≫ b ∧
        ι X T ≫ a = ι X T ≫ b :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
