module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property.Product
import StacksCheckRecall

/-!
# Products of representable morphisms having a morphism property

A property `P` as in Definition 94.10.1 that is stable under composition is
inherited by binary products of 1-morphisms of groupoid fibrations over
`(Sch/S)_fppf` that are representable by algebraic spaces and have `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 94.10.8: let `S` be a scheme in `Sch_fppf`. Let `Xᵢ`, `Yᵢ` be
categories fibred in groupoids over `(Sch/S)_fppf` for `i = 1, 2`. Let `P` be a
property of morphisms of algebraic spaces as in Definition 94.10.1 that is
stable under composition. Let `fᵢ : Xᵢ ⟶ Yᵢ` be 1-morphisms representable by
algebraic spaces. If `f₁` and `f₂` have `P`, then so does
`prodMap f₁ f₂ : prod X₁ X₂ ⟶ prod Y₁ Y₂` (Stacks `f₁ × f₂`).
Representability of the product is Lemma 94.9.10, not this conclusion. -/
@[stacks 045E]
#check (AlgebraicGeometry.Groupoids.Hom.has.prod_map :
    ∀ {S : Scheme.{u}} {X₁ X₂ Y₁ Y₂ : GroupoidsOver S}
      (P : MorphismProperty (AlgebraicSpace S))
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      [P.IsStableUnderComposition]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂),
      relativelyRepresentableByAlgebraicSpaces f₁ →
      relativelyRepresentableByAlgebraicSpaces f₂ →
      has P f₁ → has P f₂ → has P (prodMap f₁ f₂))
