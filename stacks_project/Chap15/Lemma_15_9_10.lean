module

public import ReasLib.RingTheory.Etale.IdempotentLift
import StacksCheckRecall

/-!
# Lemma 15.9.10

@stack 07M4
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

-- Lemma 15.9.10 (07M4): an idempotent in the closed fiber of an integral algebra lifts after
-- an etale base change which induces an equivalence on the closed fiber.
@[stacks 07M4]
#check
  (exists_etale_idempotent_lift_of_integral_quotient :
    (I : Ideal A) → (ebar : B ⧸ Ideal.map (algebraMap A B) I) → IsIdempotentElem ebar →
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
        (_ : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
        (e' : B ⊗[A] A'),
        IsIdempotentElem e' ∧
          TensorProduct.quotientIncludeLeft (B := B) I A' ebar =
            Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e')

#check @TensorProduct.quotientIncludeLeft
#check @TensorProduct.quotientIncludeLeft_mk

end Algebra
