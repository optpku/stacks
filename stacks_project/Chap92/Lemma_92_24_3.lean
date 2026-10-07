module

public import stacks_project.Chap92.Lemma_92_24_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of a scheme over a ring

Lemma 92.24.3 identifies `L_{X / Spec Λ}` with `L_{𝒪_X / underline{Λ}}` in
`D(𝒪_X)`, where `underline{Λ}` is the constant sheaf with value `Λ` on `X`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-- Lemma 92.24.3. Let `Λ` be a ring. Let `X` be a scheme over `Λ`. Then
`L_{X / Spec Λ} = L_{𝒪_X / underline{Λ}}` where `underline{Λ}` is the constant sheaf
with value `Λ` on `X`. -/
@[stacks 08V6]
abbrev overRingIso (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) ≅
      Cotangent.constCotangent Λ X :=
  Cotangent.overRingIso Λ X

/-- The forward map of `overRingIso` is the inverse of `overRingCompare`. -/
theorem overRingIso_hom (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    (overRingIso Λ X).hom = inv (Cotangent.overRingCompare Λ X) :=
  sorry
