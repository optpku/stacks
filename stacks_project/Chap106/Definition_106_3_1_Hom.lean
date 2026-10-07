module

public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Morphisms of thickenings of algebraic stacks

A morphism of thickenings is a pair of 1-morphisms together with a
2-isomorphism making the square with the two closed immersions 2-commute.
Over an algebraic stack `Z`, the ambient map is additionally a morphism over
`Z` via a 2-isomorphism in the triangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- A morphism of thickenings `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')` is a pair of
1-morphisms of algebraic stacks such that `f'` restricts to `f`. -/
structure Hom {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (f : X ⟶ Y) (f' : X' ⟶ Y') where
  /-- Construct a morphism of thickenings from the square 2-isomorphism. -/
  of ::
  /-- The restriction of `f'` to `X` factors as `f` through `Y`. -/
  w : f ≫ j ≅ i ≫ f'

namespace Hom

/-- Construct a morphism of thickenings from a 2-commutative square. -/
def mk {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (w : f ≫ j ≅ i ≫ f') : Hom i j f f' :=
  of w

/-- A morphism of thickenings is determined by its square 2-isomorphism. -/
theorem spec {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (h : Hom i j f f') :
    h = mk i j f f' h.w := sorry

/-- The square 2-isomorphism recovered from `Hom.mk` is the supplied cell. -/
theorem mk_w {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (w : f ≫ j ≅ i ≫ f') :
    (mk i j f f' w).w = w := sorry

end Hom

/-- A morphism of thickenings over `Z` is a morphism of thickenings whose
ambient 1-morphism is a morphism over `Z`. -/
structure HomOver {S : Scheme.{u}} {X X' Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack Z] (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (pX' : X' ⟶ Z) (pY' : Y' ⟶ Z) (f : X ⟶ Y) (f' : X' ⟶ Y')
    extends Hom i j f f' where
  /-- Construct a morphism of thickenings over `Z` from the parent square
  and the over-`Z` triangle. -/
  of ::
  /-- The ambient map `f'` fits in the 2-commutative triangle over `Z`. -/
  over_w : f' ≫ pY' ≅ pX'

namespace HomOver

/-- Construct a morphism of thickenings over `Z` from the 2-commutative square
and the over-`Z` triangle. -/
def mk {S : Scheme.{u}} {X X' Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack Z] (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (pX' : X' ⟶ Z) (pY' : Y' ⟶ Z) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (w : f ≫ j ≅ i ≫ f') (over_w : f' ≫ pY' ≅ pX') :
    HomOver i j pX' pY' f f' where
  toHom := Hom.mk i j f f' w
  over_w := over_w

/-- A morphism of thickenings over `Z` is determined by its square and triangle
2-isomorphisms. -/
theorem spec {S : Scheme.{u}} {X X' Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack Z] (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (pX' : X' ⟶ Z) (pY' : Y' ⟶ Z) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : HomOver i j pX' pY' f f') :
    h.toHom = Hom.mk i j f f' h.w ∧
      h = mk i j pX' pY' f f' h.w h.over_w := sorry

/-- The square 2-isomorphism recovered from `HomOver.mk` is the supplied cell. -/
theorem mk_w {S : Scheme.{u}} {X X' Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack Z] (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (pX' : X' ⟶ Z) (pY' : Y' ⟶ Z) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (w : f ≫ j ≅ i ≫ f') (over_w : f' ≫ pY' ≅ pX') :
    (mk i j pX' pY' f f' w over_w).w = w := sorry

/-- The triangle 2-isomorphism recovered from `HomOver.mk` is the supplied cell. -/
theorem mk_over_w {S : Scheme.{u}} {X X' Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
    [AlgebraicStack Z] (i : X ⟶ X') (j : Y ⟶ Y') [IsThickening i] [IsThickening j]
    (pX' : X' ⟶ Z) (pY' : Y' ⟶ Z) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (w : f ≫ j ≅ i ≫ f') (over_w : f' ≫ pY' ≅ pX') :
    (mk i j pX' pY' f f' w over_w).over_w = over_w := sorry

end HomOver

end AlgebraicGeometry.AlgebraicStack.IsThickening
