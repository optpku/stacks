/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Bilimit

/-!
# Bilimit stability of left-leg diagonal squares

This file contains the property-level conclusion of Stacks Project Lemma `04YR`. The chosen
self-pseudopullback cones remain explicit inputs; the construction and its computation API live
in the preceding leaves.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal.square

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Stacks Project Lemma 04YR: if `P` is a bilimit pseudopullback square, then the square
formed from the relative diagonals of its second leg and of `f` is again a bilimit square.

The two self-pseudopullback models `Q` and `R` are explicit so the statement applies to any
chosen bilimit presentations rather than only to a globally selected model. This is stated in
the represented `IsBilimit` form, so it does not require local groupoidality.
-/
@[stacks 04YR "left-leg diagonal pseudo-pullback is a bilimit"]
instance isBilimit (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [P.IsBilimit] [Q.IsBilimit] [R.IsBilimit] :
    (LeftLegDiagonal.square P Q R).IsBilimit := sorry

/-- In a locally groupoidal bicategory, the left-leg diagonal square is biterminal in the
readable cospan bicategory. This is the source-facing `(2,1)` companion of `isBilimit` above.
-/
theorem isBiterminal_of_isBilimit [IsLocallyGroupoid B]
    (P : PseudoPullbackCone f g) (Q : PseudoPullbackCone P.snd P.snd)
    (R : PseudoPullbackCone f f) [P.IsBilimit] [Q.IsBilimit] [R.IsBilimit] :
    Bicategory.IsBiterminal (LeftLegDiagonal.square P Q R) := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal.square
