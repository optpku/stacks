module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.Groupoids.Product

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

/-- The product of two 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf` that are representable by algebraic spaces is representable by
algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {X₁ X₂ Y₁ Y₂ : GroupoidsOver S} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (hf₁ : relativelyRepresentableByAlgebraicSpaces f₁)
    (hf₂ : relativelyRepresentableByAlgebraicSpaces f₂) :
    relativelyRepresentableByAlgebraicSpaces (prodMap f₁ f₂) := sorry

end AlgebraicGeometry
