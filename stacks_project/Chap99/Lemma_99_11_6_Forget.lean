/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.Forget

/-!
# The Picard groupoid fibrations and the forgetful morphism

Typed compatibility checks for the Picard groupoid fibration, its rigidification
along a section, and the morphism forgetting the trivialization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.Picard.toGroupoids :
  (f : X ⟶ B) → FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))

#check (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.toGroupoids :
  (f : X ⟶ B) → (σ : B ⟶ X) → (hσ : σ ≫ f = 𝟙 B) →
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))

#check (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.forgetHom :
  (f : X ⟶ B) → (σ : B ⟶ X) → (hσ : σ ≫ f = 𝟙 B) →
    AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.toGroupoids f σ hσ ⟶
      AlgebraicGeometry.AlgebraicSpace.Picard.toGroupoids f)
