/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.IdempotentLift
import StacksCheckRecall

/-!
# Lemma 15.9.2

@stack 07LY
-/

@[expose] public section

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

-- Lemma 15.9.2 (07LY): etale-local lifting of an idempotent modulo an ideal.
@[stacks 07LY]
#check
  (exists_etale_idempotent_lift_of_quotient :
    (I : Ideal A) → (ebar : A ⧸ I) → IsIdempotentElem ebar →
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
        (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I)) (e' : A'),
        IsIdempotentElem e' ∧
          eIso ebar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) e')

end Algebra
