/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]
variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable (sq : Bicategory.PseudoPullbackCone y p)

/-- Dotted arrows in a locally groupoidal bicategory form a groupoid.

Proof strategy: invert the ambient 2-morphism in every DottedArrow.Hom; whisker the two
compatibility equations with that inverse and use cancellation in the hom-groupoids. -/
instance categoryIsGroupoid : IsGroupoid (DottedArrow sq) := sorry

end DottedArrow

end CategoryTheory
