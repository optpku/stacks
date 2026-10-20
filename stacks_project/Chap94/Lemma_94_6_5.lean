/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {X₁ X₂ Y₁ Y₂ : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
variable (hf₁ : relativelyRepresentable f₁) (hf₂ : relativelyRepresentable f₂)

/- Lemma 94.6.5: let `S` be a scheme and let `Xᵢ`, `Yᵢ` be categories fibred in
groupoids over `Over S` for `i = 1, 2`. If `fᵢ : Xᵢ ⟶ Yᵢ` are representable
1-morphisms, then the product 1-morphism
`prodMap f₁ f₂ : prod X₁ X₂ ⟶ prod Y₁ Y₂` is a representable 1-morphism. -/
@[stacks 02ZU]
#check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.prod_map hf₁ hf₂ : relativelyRepresentable (prodMap f₁ f₂))
