/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.Forget
import StacksCheckRecall

/-!
# Lemma 99.11.6

For a morphism of algebraic spaces and a section, forgetting the trivialization
along the section is representable by schemes, surjective, and smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Lemma 99.11.6 (1): forgetting the trivialization along a section is
representable by schemes. -/
@[stacks 0D2A] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom_relativelyRepresentable :
    (f : X ⟶ B) → (σ : B ⟶ X) → (hσ : σ ≫ f = 𝟙 B) →
      ∀ ⦃U : Over S⦄
        (y : Classifying.slice U ⟶ AlgebraicGeometry.AlgebraicSpace.Picard.toGroupoids f),
        ∃ (V : Over S) (φ : V ⟶ U),
          Classifying.RepresentsBaseChange
            (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom f σ hσ) y
            (AlgebraicSpace.ofOver V) (AlgebraicSpace.ofOverMap φ))

/- Lemma 99.11.6 (2): forgetting the trivialization along a section is surjective. -/
@[stacks 0D2A] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom_surjective :
    (f : X ⟶ B) → (σ : B ⟶ X) → (hσ : σ ≫ f = 𝟙 B) →
      Classifying.Surjective
        (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom f σ hσ))

/- Lemma 99.11.6 (3): forgetting the trivialization along a section is smooth. -/
@[stacks 0D2A] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom_smooth :
    (f : X ⟶ B) → (σ : B ⟶ X) → (hσ : σ ≫ f = 𝟙 B) →
      Classifying.Smooth
        (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom f σ hσ))
