/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# Frobenius when a prime vanishes

This leaf defines the prime-power endomorphism of a commutative ring under the
condition that the prime vanishes in the ring.
-/

@[expose] public section

universe u

namespace RingHom

/-- In a commutative ring where a prime `p` vanishes, taking `p`-th powers is additive. -/
theorem add_pow_eq_of_prime_cast_eq_zero {R : Type u} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p := sorry

/-- The `p`-th power ring endomorphism of a commutative ring in which the prime `p` vanishes. -/
def frobeniusOfPrime {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' x y := add_pow_eq_of_prime_cast_eq_zero p hp x y

/-- The prime-power endomorphism sends `x` to `x ^ p`. -/
@[simp]
theorem frobeniusOfPrime_apply {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (x : R) : frobeniusOfPrime p hp x = x ^ p := sorry

end RingHom
