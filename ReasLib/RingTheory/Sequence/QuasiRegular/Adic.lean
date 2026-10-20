module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Adic.SeparatedQuotient
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Adic Quotients of Quasi-Regular Sequences

This leaf records the invariance of quasi-regularity after quotienting a
sequence and its module by the separated part of the associated adic
filtration.
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace IsQuasiRegular

/-- Lemma 10.69.9, tag `065N`: quasi-regularity is unchanged after passing
to the quotients by the intersections of the powers of the ideal generated
by the sequence. -/
@[stacks 065N "quasi-regularity and adic separated quotients"]
theorem adicSeparatedQuotient_iff {rs : List R} :
    IsQuasiRegular M rs ↔
      IsQuasiRegular
        (Ideal.adicSeparatedQuotientModule (Ideal.ofList rs) M)
        (rs.map (Ideal.Quotient.mk (Ideal.adicIntersection (Ideal.ofList rs)))) := sorry

end IsQuasiRegular

end RingTheory.Sequence
