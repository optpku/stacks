module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Invariant.FixedPoints

@[expose] public section

/-!
# Exactness of finite-group fixed points

When the order of a finite group is invertible, averaging lifts fixed points across any
surjective equivariant ring homomorphism. This is the ring-level exactness API; quotient-specific
consequences live in `Invariant.Quotient.InvertibleCard`.
@stack 0H36
-/

universe u v w

namespace FixedPoints

variable {G : Type u} [Monoid G]
variable {R : Type v} [Ring R] [MulSemiringAction G R]

/-- An element of a fixed-point subring is a unit exactly when its value in the ambient ring is a
unit. In the reverse direction, the ambient inverse is fixed automatically. -/
@[stacks 0H36 "units in a fixed-point subring"]
theorem isUnit_iff (x : FixedPoints.subring R G) :
    IsUnit x ↔ IsUnit (x : R) := sorry
-- Proof strategy: the forward implication maps a unit through the fixed-subring subtype.  For the
-- reverse implication, choose an ambient unit with value `x`; each action automorphism fixes its
-- inverse by uniqueness of inverses, so the value and inverse assemble into a unit of the fixed
-- subring.

end FixedPoints

namespace MulSemiringActionHom

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [MulSemiringAction G A] [MulSemiringAction G B]

/-- Fixed points preserve a surjective equivariant ring homomorphism when the order of the finite
acting group is a unit in the source ring. This is the reusable Reynolds-averaging statement. -/
@[stacks 0H36 "fixed points preserve surjections when the group order is invertible"]
theorem fixedPoints_surjective_of_isUnit_card [Finite G]
    (φ : A →+*[G] B) (hφ : Function.Surjective φ)
    (h_card : IsUnit (Nat.card G : A)) :
    Function.Surjective φ.fixedPoints := sorry
-- Proof strategy: install `Fintype.ofFinite G`, lift a fixed target element along `hφ`, and
-- average its orbit in `A`.  Reindexing the finite sum proves that the average is fixed;
-- equivariance of `φ` sends the sum to `Fintype.card G` copies of the target element, and the
-- inverse supplied by `h_card` cancels that scalar.  Use `Nat.card_eq_fintype_card` to return to
-- the source-facing hypothesis.

end MulSemiringActionHom
