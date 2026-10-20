module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Base change of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is stable under 2-fibre-product
base change of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces remains representable by algebraic spaces
after arbitrary 2-fibre-product base change. -/
theorem relativelyRepresentableByAlgebraicSpaces.pullback_fst
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    relativelyRepresentableByAlgebraicSpaces
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry
