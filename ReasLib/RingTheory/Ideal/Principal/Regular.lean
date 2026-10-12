/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import ReasLib.RingTheory.Ideal.Principal

/-!
# Cancellation from principal ideal products

Multiplication by a nonzerodivisor can be cancelled when testing whether an ideal is principal.
This packages the commutative-algebra step used when determinantal ideals are compared up to a
visible regular factor.
@stack 0GSW
-/

@[expose] public section

open scoped nonZeroDivisors

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- If multiplying an ideal by a regular principal ideal makes it principal, then the original
ideal is principal. -/
@[stacks 0GSW "cancellation of a regular principal ideal"]
theorem isPrincipal_of_principalIdeal_mul
    {I : Ideal R} {f : R} (hf : f ∈ nonZeroDivisors R)
    (hI : (principalIdeal f * I).IsPrincipal) : I.IsPrincipal := sorry

/-- A power of a regular principal ideal can be cancelled from a principality statement. -/
@[stacks 0GSW "cancellation of a power of a regular principal ideal"]
theorem isPrincipal_of_principalIdeal_pow_mul
    {I : Ideal R} {f : R} (hf : f ∈ nonZeroDivisors R) (n : ℕ)
    (hI : (principalIdeal (f ^ n) * I).IsPrincipal) : I.IsPrincipal := sorry

end Ideal
