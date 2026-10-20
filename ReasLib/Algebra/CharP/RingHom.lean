module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime characteristic along ring homomorphisms

This file records the characteristic transfer available when the source has
prime characteristic and the target is nontrivial.
-/

@[expose] public section

universe u v

namespace CharP

/-- A nontrivial target of a ring homomorphism has the same prime
characteristic as its source. -/
@[stacks 07FI "prime characteristic along a ring homomorphism"]
theorem of_ringHom_of_prime
    {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    [Nontrivial S] (f : R →+* S) (p : ℕ) (hp : p.Prime) [CharP R p] :
    CharP S p := sorry

end CharP

namespace RingHom

/-- An injective ring homomorphism preserves ring characteristic. -/
theorem ringChar_eq
    {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Injective f) :
    ringChar R = ringChar S := sorry

end RingHom
