module

public import ReasLib.RingTheory.Smooth.QuotientLift.Etale
import StacksCheckRecall

/-!
# Lemma 15.9.14

@stack 07M7
-/

@[expose] public section

universe u v

namespace Algebra.Smooth.QuotientLift

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

-- Lemma 15.9.14 (07M7): a map from a smooth algebra to `A ⧸ I` lifts after an etale base
-- change inducing an equivalence on that quotient.
@[stacks 07M7]
#check
  (exists_etale_lift :
    (I : Ideal A) → [Algebra.Smooth A B] → (φ : B →ₐ[A] A ⧸ I) →
      ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
        (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
        (φ' : B →ₐ[A] A'),
        ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap A A') I)).restrictScalars A).comp φ' =
          (eIso.toAlgHom.restrictScalars A).comp φ)

end Algebra.Smooth.QuotientLift
