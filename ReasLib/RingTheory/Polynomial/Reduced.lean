module

public import Mathlib.RingTheory.Polynomial.Nilpotent
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced polynomial rings

@stack 052S

This leaf owns the coefficientwise reducedness instance for one-variable polynomial
rings.  The nilpotence characterization is supplied by Mathlib; the instance is
kept here so downstream Rees-algebra and blowup arguments can use ordinary typeclass
synthesis without rebuilding the coefficient proof locally.
-/

@[expose] public section

universe u

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- A polynomial ring over a reduced commutative ring is reduced. -/
@[stacks 052S "reduced polynomial ring"]
instance instIsReduced [IsReduced R] : IsReduced (Polynomial R) := sorry

end Polynomial
