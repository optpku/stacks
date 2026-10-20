module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom

/-!
# Morphisms of thickenings of algebraic stacks

A morphism of thickenings is a pair of 1-morphisms together with a
2-isomorphism making the square with the two closed immersions 2-commute.
Over an algebraic stack `Z`, the ambient map is additionally a morphism over
`Z` via a 2-isomorphism in the triangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Definition 106.3.1 (2): a morphism of thickenings is a pair `(f, f')` with
`f' : X' ⟶ Y'` whose restriction to `X` factors through `Y`. -/
#check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.mk :
  {S : Scheme.{u}} → {X X' Y Y' : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] →
      [AlgebraicStack Y] → [AlgebraicStack Y'] →
        (i : X ⟶ X') → (j : Y ⟶ Y') →
          [IsThickening i] → [IsThickening j] →
            (f : X ⟶ Y) → (f' : X' ⟶ Y') →
              (f ≫ j ≅ i ≫ f') → IsThickening.Hom i j f f')

/- Definition 106.3.1 (3): thickenings over an algebraic stack `Z` and morphisms
of thickenings over `Z` equip the ambients with structure morphisms to `Z` so
that `f'` fits in a 2-commutative diagram. -/
#check (AlgebraicGeometry.AlgebraicStack.IsThickening.HomOver.mk :
  {S : Scheme.{u}} → {X X' Y Y' Z : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] →
      [AlgebraicStack Y] → [AlgebraicStack Y'] → [AlgebraicStack Z] →
        (i : X ⟶ X') → (j : Y ⟶ Y') →
          [IsThickening i] → [IsThickening j] →
            (pX' : X' ⟶ Z) → (pY' : Y' ⟶ Z) →
              (f : X ⟶ Y) → (f' : X' ⟶ Y') →
                (f ≫ j ≅ i ≫ f') → (f' ≫ pY' ≅ pX') →
                  IsThickening.HomOver i j pX' pY' f f')
