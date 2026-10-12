/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Pasting invertible bicategorical squares

This module owns the shape-independent horizontal pasting operation for two
invertible `2`-commutative squares. Specialized cone and dotted-arrow
constructions should reuse this datum instead of repeating the associator and
whiskering composite.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory

variable {C : Type u} [Bicategory.{w, v} C]

/-- Horizontally paste two invertible `2`-commutative squares sharing the
middle edge `k`.

Given `φ : p ≫ g ≅ q ≫ k` and `ψ : k ≫ h ≅ r ≫ l`, the result compares
`p ≫ (g ≫ h)` with `(q ≫ r) ≫ l`, with all reassociation made explicit. -/
def pasteSquareIso
    {A B D E F G : C}
    {p : A ⟶ B} {g : B ⟶ D} {q : A ⟶ E} {k : E ⟶ D}
    {h : D ⟶ G} {r : E ⟶ F} {l : F ⟶ G}
    (φ : p ≫ g ≅ q ≫ k) (ψ : k ≫ h ≅ r ≫ l) :
    p ≫ (g ≫ h) ≅ (q ≫ r) ≫ l :=
  (α_ p g h).symm ≪≫ whiskerRightIso φ h ≪≫ α_ q k h ≪≫
    whiskerLeftIso q ψ ≪≫ (α_ q r l).symm

/-- The forward cell of a pasted square is the corresponding forward
associator-and-whiskering composite. -/
@[simp]
theorem pasteSquareIso.hom
    {A B D E F G : C}
    {p : A ⟶ B} {g : B ⟶ D} {q : A ⟶ E} {k : E ⟶ D}
    {h : D ⟶ G} {r : E ⟶ F} {l : F ⟶ G}
    (φ : p ≫ g ≅ q ≫ k) (ψ : k ≫ h ≅ r ≫ l) :
    (pasteSquareIso φ ψ).hom =
      (α_ p g h).inv ≫ (whiskerRightIso φ h).hom ≫
        (α_ q k h).hom ≫ (whiskerLeftIso q ψ).hom ≫
          (α_ q r l).inv := sorry

/-- The inverse cell of a pasted square is the reverse composite of the two
inverse square comparisons and the relevant associators. -/
@[simp]
theorem pasteSquareIso.inv
    {A B D E F G : C}
    {p : A ⟶ B} {g : B ⟶ D} {q : A ⟶ E} {k : E ⟶ D}
    {h : D ⟶ G} {r : E ⟶ F} {l : F ⟶ G}
    (φ : p ≫ g ≅ q ≫ k) (ψ : k ≫ h ≅ r ≫ l) :
    (pasteSquareIso φ ψ).inv =
      (α_ q r l).hom ≫ (whiskerLeftIso q ψ).inv ≫
        (α_ q k h).inv ≫ (whiskerRightIso φ h).inv ≫
          (α_ p g h).hom := sorry

/-- Horizontal pasting of three invertible squares is associative after the
canonical reassociation of its outer boundary.

The statement retains the boundary associators explicitly because the two
parenthesizations have different source and target `1`-morphism expressions. -/
theorem pasteSquareIso.assoc
    {A B D E F G H I : C}
    {p : A ⟶ B} {g : B ⟶ D} {q : A ⟶ E} {k : E ⟶ D}
    {h : D ⟶ G} {r : E ⟶ F} {l : F ⟶ G}
    {i : G ⟶ I} {s : F ⟶ H} {m : H ⟶ I}
    (φ : p ≫ g ≅ q ≫ k) (ψ : k ≫ h ≅ r ≫ l)
    (χ : l ≫ i ≅ s ≫ m) :
    pasteSquareIso (pasteSquareIso φ ψ) χ ≪≫
        whiskerRightIso (α_ q r s) m =
      whiskerLeftIso p (α_ g h i) ≪≫
        pasteSquareIso φ (pasteSquareIso ψ χ) := sorry

/- Data and axiom audit (mathlib 4.32):

`pasteSquareIso` is a deterministic composite of associator, whiskering, and
isomorphism-composition data from the ambient bicategory. The deferred
statements expose its projections and associativity and introduce no data. -/

end CategoryTheory.Bicategory
