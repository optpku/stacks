module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism calculus for commutative squares

This leaf gives rewriting-oriented forms of a commutative square whose vertical maps are
isomorphisms.  Mathlib's `CommSq.vert_inv` packages the inverted square; the equations here
make its naturality and conjugation consequences directly available to applications.
-/

@[expose] public section

namespace CategoryTheory.CommSq.Iso

universe v u

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}
variable {f : W ⟶ X} {g : Y ⟶ Z}
variable {e : W ≅ Y} {e' : X ≅ Z}

/-- A commutative square whose vertical maps are isomorphisms identifies its horizontal
maps as objects of the arrow category. -/
noncomputable def arrowIso (top : W ⟶ X) (bottom : Y ⟶ Z)
    (left : W ⟶ Y) (right : X ⟶ Z) [IsIso left] [IsIso right]
    (sq : CommSq top left right bottom) : Arrow.mk top ≅ Arrow.mk bottom :=
  Arrow.isoMk' top bottom (asIso left) (asIso right) sq.w.symm

/-- In a commutative square with invertible vertical maps, the top morphism is an
isomorphism if and only if the bottom morphism is an isomorphism. -/
theorem isIso_top_iff_bottom (top : W ⟶ X) (bottom : Y ⟶ Z)
    (left : W ⟶ Y) (right : X ⟶ Z) [IsIso left] [IsIso right]
    (sq : CommSq top left right bottom) : IsIso top ↔ IsIso bottom := sorry

/-- Inverse naturality for a commutative square with vertical isomorphisms. -/
@[reassoc, stacks 012O "inverse naturality for a commutative square of isomorphisms"]
theorem inv_naturality (sq : CommSq f e.hom e'.hom g) :
    g ≫ e'.inv = e.inv ≫ f := sorry

/-- Conjugating the lower map by the vertical isomorphisms recovers the upper map. -/
@[reassoc, stacks 012O "upper-map computation for a commutative square of isomorphisms"]
theorem hom_comp_inv (sq : CommSq f e.hom e'.hom g) :
    e.hom ≫ g ≫ e'.inv = f := sorry

/-- Conjugating the upper map by the inverse vertical isomorphisms recovers the lower map. -/
@[reassoc, stacks 012O "lower-map computation for a commutative square of isomorphisms"]
theorem inv_comp_hom (sq : CommSq f e.hom e'.hom g) :
    e.inv ≫ f ≫ e'.hom = g := sorry

end CategoryTheory.CommSq.Iso
