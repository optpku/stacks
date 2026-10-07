module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable

/-!
# Products of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
binary products of maps of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.3.9: let `S` be a scheme. For maps `a₁ : F₁ ⟶ G₁` and
`a₂ : F₂ ⟶ G₂` of presheaves on `(Sch/S)_fppf` that are representable by
algebraic spaces, the product morphism `prod.map a₁ a₂ : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`
(Stacks `a₁ × a₂`) is representable by algebraic spaces. -/
@[stacks 046D]
theorem representableByAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (ha₁ : representableByAlgebraicSpaces a₁) (ha₂ : representableByAlgebraicSpaces a₂) :
    representableByAlgebraicSpaces (prod.map a₁ a₂) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
