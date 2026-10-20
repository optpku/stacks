module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.ReesAlgebra
public import ReasLib.RingTheory.Polynomial.Reduced

/-!
# Reduced Rees algebras

@stack 052S

This leaf owns the reducedness permanence property of the Rees-algebra
subalgebra construction.  It is separate from the grading construction so
consumers that do not use reducedness do not acquire this property API.
-/

@[expose] public section

universe u

namespace ReesAlgebra

variable {R : Type u} [CommRing R]

/-- The Rees algebra of an ideal in a reduced commutative ring is reduced. -/
@[stacks 052S "reduced Rees algebra"]
instance instIsReduced (I : Ideal R) [IsReduced R] : IsReduced (reesAlgebra I) := sorry

end ReesAlgebra
