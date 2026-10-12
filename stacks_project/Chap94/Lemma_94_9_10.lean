/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Lemma_94_6_5_Product

/-!
# Products of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is stable under binary products of
1-morphisms of groupoid fibrations over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry

/-- Lemma 94.9.10: let `S` be a scheme contained in `Sch_fppf`. Let `Xᵢ`, `Yᵢ`
be categories fibred in groupoids over `(Sch/S)_fppf` for `i = 1, 2`. If
`fᵢ : Xᵢ ⟶ Yᵢ` are 1-morphisms representable by algebraic spaces, then the
product 1-morphism `prodMap f₁ f₂ : prod X₁ X₂ ⟶ prod Y₁ Y₂` is a 1-morphism
representable by algebraic spaces. -/
@[stacks 0303]
theorem relativelyRepresentableByAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {X₁ X₂ Y₁ Y₂ : GroupoidsOver S} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (hf₁ : relativelyRepresentableByAlgebraicSpaces f₁)
    (hf₂ : relativelyRepresentableByAlgebraicSpaces f₂) :
    relativelyRepresentableByAlgebraicSpaces (prodMap f₁ f₂) := sorry

end AlgebraicGeometry
