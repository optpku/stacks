/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Basic

/-!
# Bilimit invariance under pseudopullback symmetry

This property leaf transports the shape-independent bilimit predicate across the explicit
involution on readable pseudopullback-cone data.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Explicitly transport a bilimit witness across the swap of a readable pseudopullback cone. -/
theorem swap.isBilimitOf (P : PseudoPullbackCone f g) (h : P.IsBilimit) :
    P.swap.IsBilimit := sorry

/-- The swap of a bilimit readable pseudopullback cone is canonically bilimit. -/
instance swap.isBilimit (P : PseudoPullbackCone f g) [P.IsBilimit] :
    P.swap.IsBilimit := sorry

/-- A readable pseudopullback cone is bilimit whenever its swap is bilimit. -/
theorem isBilimitOfSwap (P : PseudoPullbackCone f g) (h : P.swap.IsBilimit) :
    P.IsBilimit := sorry

/-- Reversing the two legs does not change whether a readable pseudopullback cone is a
bilimit. -/
@[simp]
theorem swap.isBilimit_iff (P : PseudoPullbackCone f g) :
    P.swap.IsBilimit ↔ P.IsBilimit := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
