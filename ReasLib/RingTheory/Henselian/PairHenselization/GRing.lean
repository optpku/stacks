module

public import ReasLib.RingTheory.Henselian.PairHenselization
public import ReasLib.RingTheory.Regular.GRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# G-rings and henselizations of pairs

@stack 0AH3
@stack 0AH5

The G-ring permanence theorem is kept in this narrow bridge leaf so that the
intrinsic pair-henselization owner does not depend on the regular-map stack.
-/

universe u v

namespace IsPairHenselization

variable {B : Type u} [CommRing B] {J : Ideal B}
variable {A : Type v} [CommRing A] [Algebra B A] {I : Ideal A}

/-- Lemma 15.50.15 (Tag 0AH3): a henselization along an ideal of a G-ring is
again a G-ring. -/
@[stacks 0AH3]
theorem isGRing [IsGRing B] [IsPairHenselization B J A I] : IsGRing A := sorry

namespace AdicCompletion

/-- The adic completion map of a pair henselization over a G-ring is regular. -/
@[stacks 0AH5 "regular completion map of a pair henselization"]
theorem regularMap [IsGRing B] [IsPairHenselization B J A I] :
    (algebraMap A (_root_.AdicCompletion I A)).Regular := sorry

end AdicCompletion

end IsPairHenselization
