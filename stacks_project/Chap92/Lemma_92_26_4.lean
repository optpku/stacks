/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_26_4_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of an algebraic space over a ring

Lemma 92.26.4 identifies `L_{X / Spec Λ}` with `L_{𝒪_X / underline{Λ}}` in
`D(𝒪_X)`, where `underline{Λ}` is the constant sheaf with value `Λ` on `X_étale`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

noncomputable section

universe u

/-- Lemma 92.26.4. Let `Λ` be a ring. Let `X` be an algebraic space over `Λ`. Then
`L_{X / Spec Λ} = L_{𝒪_X / underline{Λ}}` where `underline{Λ}` is the constant sheaf
with value `Λ` on `X_étale`. -/
@[stacks 08VG]
abbrev spaceOverRingIso (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    Cotangent.cotangent (toBase X) ≅ Cotangent.constCotangent Λ X :=
  Cotangent.spaceOverRingIso Λ X

/-- The forward map of `spaceOverRingIso` is the inverse of `spaceOverRingCompare`. -/
theorem spaceOverRingIso_hom (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)) :
    (spaceOverRingIso Λ X).hom = inv (Cotangent.spaceOverRingCompare Λ X) :=
  sorry
