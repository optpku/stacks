/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.«88_27_0_1_Completion»
public import stacks_project.Chap88.Lemma_88_25_5_MapAlong

/-!
# Uniqueness of morphisms after checking the open complement and a map of completions

A morphism of locally Noetherian algebraic spaces is uniquely determined by its
restriction to the open complement of a closed subset and the induced map of
completions, when both morphisms send that closed subset into a given closed
subset of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Lemma 88.25.5: Let `S` be a scheme. Let `X`, `Y` be locally Noetherian
algebraic spaces over `S`. Let `T ⊂ Points X` and `T' ⊂ Points Y` be closed.
Let `a, b : X ⟶ Y` be morphisms of algebraic spaces over `S` such that
`a|_{X \ T} = b|_{X \ T}`, such that `|a|(T) ⊂ T'` and `|b|(T) ⊂ T'`, and such
that `a_/T = b_/T` as morphisms `X_/T ⟶ Y_/T'`. Then `a = b`.

Here `a|_{X \ T}` is `openComplementι X T ≫ a`, `|a|(T) ⊂ T'` is
`Points.map a '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))`, and `a_/T` is
`mapOfLe a T T' ha : completionAlong X T ⟶ completionAlong Y T'`. -/
@[stacks 0AR7]
theorem eq_of_mapOfLe_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (T : Closeds (Points X)) (T' : Closeds (Points Y)) {a b : X ⟶ Y}
    (h_open : openComplementι X T ≫ a = openComplementι X T ≫ b)
    (ha : Points.map a '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    (hb : Points.map b '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    (h_completion : mapOfLe a T T' ha = mapOfLe b T T' hb) :
    a = b :=
  sorry

/-- Morphisms of locally Noetherian algebraic spaces are equal if and only if they
agree on the open complement of `T` and after mapping completions along `T`
into `T'`. -/
theorem eq_iff_mapOfLe_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (T : Closeds (Points X)) (T' : Closeds (Points Y)) {a b : X ⟶ Y}
    (ha : Points.map a '' (T : Set (Points X)) ⊆ (T' : Set (Points Y)))
    (hb : Points.map b '' (T : Set (Points X)) ⊆ (T' : Set (Points Y))) :
    a = b ↔
      openComplementι X T ≫ a = openComplementι X T ≫ b ∧
        mapOfLe a T T' ha = mapOfLe b T T' hb :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
