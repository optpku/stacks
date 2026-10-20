module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Product
import StacksCheckRecall

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

/- Lemma 94.9.10: let `S` be a scheme contained in `Sch_fppf`. Let `Xᵢ`, `Yᵢ`
be categories fibred in groupoids over `(Sch/S)_fppf` for `i = 1, 2`. If
`fᵢ : Xᵢ ⟶ Yᵢ` are 1-morphisms representable by algebraic spaces, then the
product 1-morphism `prodMap f₁ f₂ : prod X₁ X₂ ⟶ prod Y₁ Y₂` is a 1-morphism
representable by algebraic spaces. -/
@[stacks 0303]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.prod_map :
    ∀ {S : Scheme.{u}} {X₁ X₂ Y₁ Y₂ : GroupoidsOver S}
      {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂},
      relativelyRepresentableByAlgebraicSpaces f₁ →
      relativelyRepresentableByAlgebraicSpaces f₂ →
      relativelyRepresentableByAlgebraicSpaces (prodMap f₁ f₂))
