/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.SubringPair
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Intersections of subrings as ring pullbacks

For two subrings of a common field, their intersection is canonically
ring-equivalent to the pullback of their subtype homomorphisms.
-/

@[expose] public section

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

/-- The canonical homomorphism from the intersection of two subrings to the
pullback of their inclusions into the ambient field. -/
@[stacks 09MY "fraction-ring intersection map to pullback"]
def intersectionToPullback (P : FractionRing.SubringPair K) :
    P.intersection →+* RingHom.pullback P.left.subtype P.right.subtype :=
  (P.toLeft.prod P.toRight).codRestrict
    (RingHom.pullback P.left.subtype P.right.subtype) fun _ ↦ rfl

/-- The canonical homomorphism from the pullback of two subring inclusions to
their intersection. -/
@[stacks 09MY "fraction-ring pullback map to intersection"]
def pullbackToIntersection (P : FractionRing.SubringPair K) :
    RingHom.pullback P.left.subtype P.right.subtype →+* P.intersection where
  toFun x :=
    ⟨x.1.1, x.1.1.2, by
      have hx : (x.1.1 : K) = (x.1.2 : K) := x.2
      rw [hx]
      exact x.1.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The intersection of two subrings of a common field is canonically
ring-equivalent to the pullback of their inclusion homomorphisms. -/
@[stacks 09MY "fraction-ring intersection equivalence with pullback"]
def intersectionEquivPullback (P : FractionRing.SubringPair K) :
    P.intersection ≃+* RingHom.pullback P.left.subtype P.right.subtype where
  toFun := P.intersectionToPullback
  invFun := P.pullbackToIntersection
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (Prod.ext rfl (Subtype.ext x.2))
  map_mul' := map_mul P.intersectionToPullback
  map_add' := map_add P.intersectionToPullback

/-- The first pullback projection of the intersection equivalence is the
canonical inclusion into the left subring. -/
theorem intersectionEquivPullback_apply_fst (P : FractionRing.SubringPair K)
    (x : P.intersection) :
    RingHom.pullbackFst P.left.subtype P.right.subtype
        (P.intersectionEquivPullback x) = P.toLeft x := sorry

/-- The second pullback projection of the intersection equivalence is the
canonical inclusion into the right subring. -/
theorem intersectionEquivPullback_apply_snd (P : FractionRing.SubringPair K)
    (x : P.intersection) :
    RingHom.pullbackSnd P.left.subtype P.right.subtype
        (P.intersectionEquivPullback x) = P.toRight x := sorry

end FractionRing.SubringPair
