/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Uniqueness of morphisms after checking the open complement and the completion

A morphism from a locally Noetherian algebraic space to an arbitrary algebraic
space is uniquely determined by its restrictions to the open complement of a
closed subset and to the completion along that subset. For a locally Noetherian
target, equality of the induced maps between completions also suffices when both
morphisms send the source closed subset into a given closed subset of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Morphisms from a locally Noetherian algebraic space to an arbitrary algebraic
space are equal if they agree on the open complement of a closed subset and
after precomposition with the canonical inclusion of its completion. -/
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

/-- Morphisms between locally Noetherian algebraic spaces are equal if they agree
on the open complement of a closed subset and induce equal maps of completions
into a closed subset containing both images. -/
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
