module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Product
import StacksCheckRecall

/-!
# Products of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
binary products of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 80.3.9: let `S` be a scheme. For maps `a₁ : F₁ ⟶ G₁` and
`a₂ : F₂ ⟶ G₂` of presheaves on `(Sch/S)_fppf` that are representable by
algebraic spaces, the product morphism `prod.map a₁ a₂ : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`
(Stacks `a₁ × a₂`) is representable by algebraic spaces. -/
@[stacks 046D]
#check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.prod_map :
  ∀ {S : Scheme.{u}} {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u}
    (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂),
    AlgebraicSpace.representableByAlgebraicSpaces a₁ →
    AlgebraicSpace.representableByAlgebraicSpaces a₂ →
    AlgebraicSpace.representableByAlgebraicSpaces (prod.map a₁ a₂))
