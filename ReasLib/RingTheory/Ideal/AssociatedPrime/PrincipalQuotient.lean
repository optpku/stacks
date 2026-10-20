module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Quotient.Minimal
public import ReasLib.RingTheory.Ideal.Principal.Height
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated primes of principal quotients

The absence of embedded primes and the height calculation are deliberately separate: the first
does not require the principal ideal to be nonzero, while the second does.

@stack 031T
-/

@[expose] public section

universe u

namespace embeddedAssociatedPrimes

variable {R : Type u} [CommRing R] [IsDomain R] [R ⊧ (S₂)]

/-- A principal quotient of an `(S₂)` domain has no embedded associated primes. -/
@[stacks 031T "principal quotients have no embedded primes"]
theorem quotient_eq_empty_of_isPrincipal (I : Ideal R) [I.IsPrincipal] :
    embeddedAssociatedPrimes R (R ⧸ I) = ∅ := sorry

end embeddedAssociatedPrimes

namespace associatedPrimes.Quotient

variable {R : Type u} [CommRing R] [IsDomain R] [R ⊧ (S₂)]

/-- Every associated prime of a nonzero principal quotient of an `(S₂)` domain has height one. -/
@[stacks 031T "height of associated primes of a principal quotient"]
theorem height_eq_one_of_isPrincipal
    (I : Ideal R) [I.IsPrincipal] (hI : I ≠ ⊥)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ I)) :
    p.height = 1 :=
  Ideal.height_eq_one_of_isPrincipal_of_mem_minimalPrimes I hI p <|
    mem_minimalPrimes_of_noEmbedded I
      (embeddedAssociatedPrimes.quotient_eq_empty_of_isPrincipal I) hp

end associatedPrimes.Quotient
