module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Equivalence-invariance of morphisms representable by algebraic spaces

Relative representability by algebraic spaces is invariant under 2-commutative
squares of 1-morphisms of groupoid fibrations over `(Sch/S)_fppf` whose
horizontal arrows are equivalences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- In a square of morphisms of categories fibred in groupoids over `(Sch/S)_fppf`
that commutes up to an invertible 2-cell, equivalences on the horizontal sides
preserve and reflect representability of the vertical morphisms by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.iff_of_equivalence
    {S : Scheme.{u}} {X' X Y' Y : GroupoidsOver S}
    (eX : X' ≌ X) (eY : Y' ≌ Y) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (sq : eX.hom ≫ f ≅ f' ≫ eY.hom) :
    relativelyRepresentableByAlgebraicSpaces f ↔
      relativelyRepresentableByAlgebraicSpaces f' := sorry

end AlgebraicGeometry
