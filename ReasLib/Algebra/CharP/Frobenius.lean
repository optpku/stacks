module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# Frobenius when a prime vanishes

This leaf defines the prime-power endomorphism of a commutative ring under the
condition that the prime vanishes in the ring.
-/

@[expose] public section

universe u v

namespace RingHom

/-- In a commutative ring where a prime `p` vanishes, taking `p`-th powers is additive. -/
theorem add_pow_eq_of_prime_cast_eq_zero {R : Type u} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0) (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p := sorry

/-- A ring homomorphism transports the vanishing of a natural-number cast. -/
theorem natCast_eq_zero_of_eq_zero {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (n : ℕ) (f : A →+* B) (h : (n : A) = 0) : (n : B) = 0 := by
  rw [← map_natCast f n, h, map_zero]

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

/-- Explicit-proof Frobenius endomorphisms commute with ring homomorphisms. -/
theorem frobeniusOfPrime_naturality {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (p : ℕ) [Fact p.Prime] (f : A →+* B) (hpA : (p : A) = 0) (hpB : (p : B) = 0) :
    f.comp (frobeniusOfPrime p hpA) = (frobeniusOfPrime p hpB).comp f := by
  ext x
  simp only [RingHom.comp_apply, frobeniusOfPrime_apply]
  exact map_pow f x p

end RingHom
