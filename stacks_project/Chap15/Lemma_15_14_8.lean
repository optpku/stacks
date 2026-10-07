module

public import ReasLib.RingTheory.Henselian.AbsolutelyIntegrallyClosed
import StacksCheckRecall

/-!
# Lemma 15.14.8

@stack 0DCT
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]

-- Lemma 15.14.8 (0DCT): the henselian criterion for an ideal in an absolutely integrally
-- closed ring, with the source's bijectivity condition on idempotents.
@[stacks 0DCT]
#check
  (henselianRing_iff_le_jacobson_and_bijective_on_idempotents :
    (I : Ideal A) → HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧ Function.Bijective (Ideal.Quotient.mk I).idempotentMap)

#check @henselianRing_iff_le_jacobson_and_surjective_on_idempotents

end Ideal
