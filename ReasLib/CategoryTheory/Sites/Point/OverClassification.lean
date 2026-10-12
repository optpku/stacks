/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Map
public import Mathlib.CategoryTheory.Sites.Point.Over

/-!
# Points over a localized site point

This module gives the isomorphism-class formulation of the relation between a
point of a slice site and its image in the ambient site.  It deliberately does
not choose a lying-over isomorphism: that coherent datum belongs to an
iso-comma/groupoid refinement rather than to the reusable proposition-level
API here.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point.Over

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/-- A point of the slice site lies over `p` when its image under the slice forgetful functor is
isomorphic to `p`.  This is the invariant, isomorphism-class relation; it does not retain a chosen
comparison isomorphism. -/
def LiesOver (p : Point.{w} J) {U : C} (q : Point.{w} (J.over U)) : Prop :=
  IsIsomorphic (q.map (Over.forget U) J) p

/-- Every localized point constructed from an element of `p.fiber.obj U` lies over `p`. -/
theorem over_liesOver (p : Point.{w} J) (U : C) (x : p.fiber.obj U) :
    LiesOver p (p.over x) := sorry

/-- A point of the slice site that lies over `p` is isomorphic to one obtained by localizing `p`
at an element of `p.fiber.obj U`. -/
theorem exists_isomorphic_over_of_liesOver
    (p : Point.{w} J) {U : C} (q : Point.{w} (J.over U)) (hq : LiesOver p q) :
    ∃ x : p.fiber.obj U, IsIsomorphic q (p.over x) := sorry

/-- Isomorphism-class classification of points of the slice site lying over `p`. -/
theorem liesOver_iff_exists_isomorphic_over
    (p : Point.{w} J) (U : C) (q : Point.{w} (J.over U)) :
    LiesOver p q ↔ ∃ x : p.fiber.obj U, IsIsomorphic q (p.over x) := sorry

end CategoryTheory.GrothendieckTopology.Point.Over
