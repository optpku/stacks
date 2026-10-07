module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Powers and order of vanishing

This leaf complements Mathlib's exact power formula for nonzerodivisors with
the subadditive upper bound valid for every element of a commutative ring.

@stack 0BWS
-/

universe u

namespace Ring

variable {R : Type u} [CommRing R]

/-- The order of vanishing of a product is at most the sum of the orders of
vanishing of its factors. -/
@[stacks 0BWS "order-of-vanishing product upper bound"]
theorem ord_mul_le (x y : R) :
    ord R (x * y) ≤ ord R x + ord R y := sorry

/-- The order of vanishing of a power is at most the corresponding multiple of
the order of vanishing of the element. -/
@[stacks 0BWS "order-of-vanishing power upper bound"]
theorem ord_pow_le (x : R) (n : ℕ) :
    ord R (x ^ n) ≤ n • ord R x := sorry

end Ring
