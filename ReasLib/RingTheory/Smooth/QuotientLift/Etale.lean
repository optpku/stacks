module

public import Mathlib.RingTheory.Etale.Basic
public import ReasLib.RingTheory.Smooth.QuotientLift.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale lifts of smooth maps to quotients

@stack 07M7

A map from a smooth algebra to a quotient lifts after an etale base change which leaves the
quotient unchanged.
-/

@[expose] public section

universe u v

namespace Algebra.Smooth.QuotientLift

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.9.14 (Stacks `07M7`): a map from a smooth `A`-algebra to `A ⧸ I` lifts to an
etale `A`-algebra whose reduction modulo `I` is equivalent to `A ⧸ I`. -/
@[stacks 07M7]
theorem exists_etale_lift (I : Ideal A) [Algebra.Smooth A B] (φ : B →ₐ[A] A ⧸ I) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (φ' : B →ₐ[A] A'),
      ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap A A') I)).restrictScalars A).comp φ' =
        (eIso.toAlgHom.restrictScalars A).comp φ := sorry

end Algebra.Smooth.QuotientLift
