/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.Stack
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Forgetting the rigidification of a Picard object along a section
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard category rigidified along a section, bundled as a category fibred
in groupoids over `Over S`, with Hom-universe `u + 1`. -/
def toGroupoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f σ hσ)

/-- The projection of the rigidified Picard groupoid fibration is the rigidified
Picard projection. -/
theorem toGroupoids_p (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    (toGroupoids f σ hσ).p = p f σ hσ := sorry

/-- The total category of the rigidified Picard groupoid fibration is the category
of rigidified Picard objects. -/
theorem toGroupoids_total (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    (toGroupoids f σ hσ).total = Obj f σ hσ := sorry

/-- The morphism of groupoid fibrations forgetting the trivialization of a Picard
object along a section. -/
def forgetHom (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    toGroupoids f σ hσ ⟶ Picard.toGroupoids f :=
  Groupoids.ofBasedFunctor
    { toFunctor := forget f σ hσ
      w := (p_eq_forget_comp f σ hσ).symm }

/-- The functor underlying the forgetful morphism forgets the trivialization
along the section. -/
theorem forgetHom_toFunctor (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Groupoids.toFunctor (forgetHom f σ hσ) = forget f σ hσ := sorry

/-- The forgetful morphism of rigidified Picard groupoid fibrations commutes
strictly with the projections to `Over S`. -/
theorem forgetHom_comm (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Groupoids.toFunctor (forgetHom f σ hσ) ⋙ Picard.p f = p f σ hσ := sorry

/-- Every base change of the forgetful morphism from the rigidified Picard
groupoid fibration along a scheme is represented by a scheme. -/
theorem forgetHom_relativelyRepresentable (f : X ⟶ B) (σ : B ⟶ X)
    (hσ : σ ≫ f = 𝟙 B) :
    ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Picard.toGroupoids f),
      ∃ (V : Over S) (φ : V ⟶ U),
        Classifying.RepresentsBaseChange (forgetHom f σ hσ) y
          (AlgebraicSpace.ofOver V) (AlgebraicSpace.ofOverMap φ) := sorry

/-- Forgetting the trivialization along a section is a surjective morphism of
Picard groupoid fibrations. -/
instance forgetHom_surjective (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Classifying.Surjective (forgetHom f σ hσ) := sorry

/-- Forgetting the trivialization along a section is a smooth morphism of
Picard groupoid fibrations. -/
instance forgetHom_smooth (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    Classifying.Smooth (forgetHom f σ hσ) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
