module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite denominator clearing at a prime localization

This leaf turns Mathlib's finite common-multiple theorem for a localization
into the equality form naturally used for localization at a prime ideal.
It introduces no chosen denominator or numerator data.
-/

@[expose] public section

universe u v

namespace Localization.AtPrime

variable {R : Type u} [CommSemiring R]

/-- A finite family in `Localization.AtPrime p` has a common denominator outside `p`, with a
numerator in `R` for each member of the family. This is the equality-form specialization of
`IsLocalization.exist_integer_multiples_of_finite` to `Localization.AtPrime p`. -/
@[stacks 00QR "prime-localization common denominator"]
theorem exists_commonDenom
    (p : Ideal R) [p.IsPrime] {ι : Type v} [Finite ι]
    (x : ι → Localization.AtPrime p) :
    ∃ (f : R) (_ : f ∉ p) (a : ι → R), ∀ i,
      algebraMap R (Localization.AtPrime p) f * x i =
        algebraMap R (Localization.AtPrime p) (a i) := sorry

end Localization.AtPrime
