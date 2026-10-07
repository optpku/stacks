module

public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

/-!
# Localizing the integers at a prime

This file names the canonical Lean model of the `p`-local integers `ℤ_(p)`.  Mathlib's
`Int.ideal_span_isMaximal_of_prime`, followed by its canonical maximal-to-prime instance, supplies
the primality needed by `Localization.AtPrime`.
-/

namespace Int

/-- The `p`-local integers `ℤ_(p)`, obtained by inverting the integers outside `(p)`. -/
@[stacks 07KD "p-local integers"]
abbrev LocalizationAtPrime (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))

end Int
