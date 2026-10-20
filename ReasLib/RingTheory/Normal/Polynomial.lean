module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Normal Polynomial Rings

This leaf records the polynomial-ring permanence of normality.

@stack 00H1
-/

universe u

namespace IsNormalRing

/-- Lemma 10.37.14, tag `00H1`: a polynomial ring over a normal ring is
normal. -/
@[stacks 00H1]
theorem polynomial {R : Type u} [CommRing R] [IsNormalRing R] :
    IsNormalRing (Polynomial R) := sorry

end IsNormalRing

namespace Polynomial

/-- Polynomial rings over normal rings carry the canonical normal-ring
instance. -/
instance instIsNormalRing {R : Type u} [CommRing R] [IsNormalRing R] :
    IsNormalRing (Polynomial R) := sorry

end Polynomial
