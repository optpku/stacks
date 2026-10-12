/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_11_6_Forget

/-!
# Lemma 99.11.6

In Situation 99.11.1, if `σ : B ⟶ X` is a section of `f : X ⟶ B`, the
forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` is
representable, surjective, and smooth. Representable means the 2-fibre
product against a test object is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard
namespace WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.6 (1): in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B`, the 2-fibre product of the forgetful 1-morphism
`Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}` against a test object is
representable by a scheme. -/
@[stacks 0D2A]
theorem forgetHom_relativelyRepresentable (f : X ⟶ B) (σ : B ⟶ X)
    (hσ : σ ≫ f = 𝟙 B) :
    ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Picard.toGroupoids f),
      ∃ (V : Over S) (φ : V ⟶ U),
        Classifying.RepresentsBaseChange (forgetHom f σ hσ) y
          (AlgebraicSpace.ofOver V) (AlgebraicSpace.ofOverMap φ) :=
  sorry

/-- Lemma 99.11.6 (2): in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B`, the forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`
is surjective. -/
@[stacks 0D2A]
instance forgetHom_surjective (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Classifying.Surjective (forgetHom f σ hσ) :=
  sorry

/-- Lemma 99.11.6 (3): in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B`, the forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`
is smooth. -/
@[stacks 0D2A]
instance forgetHom_smooth (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Classifying.Smooth (forgetHom f σ hσ) :=
  sorry

end WithSection
end AlgebraicGeometry.AlgebraicSpace.Picard
