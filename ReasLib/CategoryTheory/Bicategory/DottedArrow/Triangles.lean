/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone.ReplaceIso

/-!
# Two-triangle fill-ins of a 2-commutative square

A `DottedArrow` records a fill-in of a `PseudoPullbackCone` together with the
coherence that the two triangular 2-isomorphisms compose to the chosen outer
2-cell. Dropping that coherence leaves the raw two-triangle data used to state
existence of a fill-in without comparing 2-morphisms. Changing the outer 2-cell
of a cone, with the same apex and projections, is `replaceIso`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.DottedArrow

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}

/-- A two-triangle fill-in of a 2-commutative square is a dotted morphism
together with triangular 2-isomorphisms, without requiring those 2-cells to
compose to the chosen outer comparison. -/
structure Triangles (sq : Bicategory.PseudoPullbackCone y p) where
  /-- The dotted morphism from the lower-left object to the upper-right object. -/
  arrow : T ⟶ X
  /-- The comparison 2-isomorphism for the upper-left triangle. -/
  left : sq.fst ≫ arrow ≅ sq.snd
  /-- The comparison 2-isomorphism for the lower-right triangle. -/
  right : y ≅ arrow ≫ p

namespace Triangles

variable {sq : Bicategory.PseudoPullbackCone y p}

/-- Assemble a two-triangle fill-in from a dotted morphism and two triangular
2-isomorphisms. -/
def of (arrow : T ⟶ X) (left : sq.fst ≫ arrow ≅ sq.snd)
    (right : y ≅ arrow ≫ p) : Triangles sq where
  arrow := arrow
  left := left
  right := right

/-- The dotted morphism of `Triangles.of` is the supplied morphism. -/
@[simp]
theorem of_arrow (arrow : T ⟶ X) (left : sq.fst ≫ arrow ≅ sq.snd)
    (right : y ≅ arrow ≫ p) : (of arrow left right).arrow = arrow :=
  sorry

/-- The upper-left comparison of `Triangles.of` is the supplied 2-isomorphism. -/
@[simp]
theorem of_left (arrow : T ⟶ X) (left : sq.fst ≫ arrow ≅ sq.snd)
    (right : y ≅ arrow ≫ p) : (of arrow left right).left = left :=
  sorry

/-- The lower-right comparison of `Triangles.of` is the supplied 2-isomorphism. -/
@[simp]
theorem of_right (arrow : T ⟶ X) (left : sq.fst ≫ arrow ≅ sq.snd)
    (right : y ≅ arrow ≫ p) : (of arrow left right).right = right :=
  sorry

/-- The composite 2-isomorphism of the two triangles, obtained by whiskering
the lower-right comparison, reassociating, and whiskering the upper-left
comparison. This is the cell that `DottedArrow.comm` compares with `sq.iso`. -/
abbrev outerIso (A : Triangles sq) : sq.fst ≫ y ≅ sq.snd ≫ p :=
  whiskerLeftIso sq.fst A.right ≪≫
    (α_ sq.fst A.arrow p).symm ≪≫ whiskerRightIso A.left p

/-- Promote a two-triangle fill-in to a dotted arrow once the composite of the
triangles equals the chosen outer comparison. -/
def toDottedArrow (A : Triangles sq) (h : A.outerIso = sq.iso) : DottedArrow sq where
  arrow := A.arrow
  left := A.left
  right := A.right
  comm := h

/-- The dotted morphism of `toDottedArrow` is the original dotted morphism. -/
@[simp]
theorem toDottedArrow_arrow (A : Triangles sq) (h : A.outerIso = sq.iso) :
    (toDottedArrow A h).arrow = A.arrow :=
  sorry

/-- The upper-left comparison of `toDottedArrow` is the original comparison. -/
@[simp]
theorem toDottedArrow_left (A : Triangles sq) (h : A.outerIso = sq.iso) :
    (toDottedArrow A h).left = A.left :=
  sorry

/-- The lower-right comparison of `toDottedArrow` is the original comparison. -/
@[simp]
theorem toDottedArrow_right (A : Triangles sq) (h : A.outerIso = sq.iso) :
    (toDottedArrow A h).right = A.right :=
  sorry

end Triangles

variable {sq : Bicategory.PseudoPullbackCone y p}

/-- Forget the outer-coherence condition of a dotted arrow, retaining the two
triangular 2-isomorphisms. -/
def toTriangles (A : DottedArrow sq) : Triangles sq where
  arrow := A.arrow
  left := A.left
  right := A.right

/-- The dotted morphism of `toTriangles` is the original dotted morphism. -/
@[simp]
theorem toTriangles_arrow (A : DottedArrow sq) :
    (toTriangles A).arrow = A.arrow :=
  sorry

/-- The upper-left comparison of `toTriangles` is the original comparison. -/
@[simp]
theorem toTriangles_left (A : DottedArrow sq) :
    (toTriangles A).left = A.left :=
  sorry

/-- The lower-right comparison of `toTriangles` is the original comparison. -/
@[simp]
theorem toTriangles_right (A : DottedArrow sq) :
    (toTriangles A).right = A.right :=
  sorry

/-- For a coherent dotted arrow, the composite of the two triangles is the
chosen outer comparison. -/
theorem outerIso_eq_iso_of_dottedArrow (A : DottedArrow sq) :
    (toTriangles A).outerIso = sq.iso :=
  sorry

end CategoryTheory.DottedArrow
