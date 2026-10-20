/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Etale-local lifting of polynomial factorizations

@stack 0ALH
@stack 07M1

Coprime polynomial factorizations modulo an ideal lift after an etale base change which leaves the
quotient unchanged.  The monic and unit-leading-coefficient forms are exposed separately.
-/

open Polynomial

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Lemma 15.9.5: a coprime factorization of a monic polynomial into monic factors modulo an
ideal lifts after an etale base change which induces an equivalence on the quotient. -/
@[stacks 0ALH]
theorem exists_etale_lift_factorization_of_monic_mod_ideal
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X])
    (hf : f.Monic) (hgbar : gbar.Monic) (hhbar : hbar.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I]
        (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
      g'.Monic ∧ h'.Monic ∧
        f.map (algebraMap A A') = g' * h' ∧
        gbar.map quotientAlgEquiv.toRingHom =
          g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
        hbar.map quotientAlgEquiv.toRingHom =
          h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := sorry

/-- Lemma 15.9.6: a coprime factorization of a monic polynomial modulo an ideal lifts etale
locally when the leading coefficient of the first factor is a unit. -/
@[stacks 07M1]
theorem exists_etale_factorization_lift_of_isUnit_leadingCoeff
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hunit : IsUnit gbar.leadingCoeff) (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I]
        (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
      f.map (algebraMap A A') = g' * h' ∧
        gbar.map quotientAlgEquiv.toRingHom =
          g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
        hbar.map quotientAlgEquiv.toRingHom =
          h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := sorry

end Algebra
