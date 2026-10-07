module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap99.Lemma_99_10_1_Picard
public import stacks_project.Chap99.Lemma_99_11_5
public import stacks_project.Chap99.Lemma_99_11_7_WithSection
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# The forgetful 1-morphism of Picard stacks with a section

Situation 99.11.1 supplies `Picardstack_{X/B}` and, for a section `σ` of
`f : X ⟶ B`, the rigidified stack `Picardstack_{X/B, σ}`. This module packages
the forgetful functor as a 1-morphism of categories fibred in groupoids over
`Over S`, at Hom-universe `u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard category of `f`, bundled as a category fibred in groupoids over
`Over S`. The Hom-universe is `u + 1` because Picard morphisms include module
isomorphisms on the large étale site, so this cannot land in `GroupoidsOver S`. -/
def toGroupoids (f : X ⟶ B) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of `toGroupoids f` is the source functor `p f`. -/
theorem toGroupoids_p (f : X ⟶ B) : (toGroupoids f).p = p f := sorry

/-- The total category of `toGroupoids f` is the category `Obj f`. -/
theorem toGroupoids_total (f : X ⟶ B) : (toGroupoids f).total = Obj f := sorry

namespace WithSection

/-- The Picard category of `f` with a chosen section `σ`, bundled as a category
fibred in groupoids over `Over S`. The Hom-universe is `u + 1` for the same
reason as `Picard.toGroupoids`. -/
def toGroupoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f σ hσ)

/-- The projection of `toGroupoids f σ hσ` is the source functor `p f σ hσ`. -/
theorem toGroupoids_p (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    (toGroupoids f σ hσ).p = p f σ hσ := sorry

/-- The total category of `toGroupoids f σ hσ` is the category `Obj f σ hσ`. -/
theorem toGroupoids_total (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    (toGroupoids f σ hσ).total = Obj f σ hσ := sorry

/-- The forgetful 1-morphism `Picardstack_{X/B, σ} ⟶ Picardstack_{X/B}`,
packaged as a morphism of categories fibred in groupoids over `Over S`. The
underlying functor is `forget`. -/
def forgetHom (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    toGroupoids f σ hσ ⟶ Picard.toGroupoids f :=
  Groupoids.ofBasedFunctor
    { toFunctor := forget f σ hσ
      w := sorry }

/-- The underlying functor of `forgetHom` is the forgetful functor on Picard
objects with a section. -/
theorem forgetHom_toFunctor (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Groupoids.toFunctor (forgetHom f σ hσ) = forget f σ hσ := sorry

/-- `forgetHom` lies strictly over `Over S`. -/
theorem forgetHom_comm (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Groupoids.toFunctor (forgetHom f σ hσ) ⋙ Picard.p f = p f σ hσ := sorry

end WithSection

end AlgebraicGeometry.AlgebraicSpace.Picard
