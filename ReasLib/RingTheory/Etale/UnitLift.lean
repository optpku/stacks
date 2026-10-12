/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Etale-local lifting of units

@stack 07LX

A unit modulo an ideal lifts to a unit after an etale base change which leaves the quotient
unchanged.  A companion exposes the canonical away-localization model used for this lift.
-/

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Lemma 15.9.1: a unit in `A ⧸ I` lifts to a unit after an etale base change inducing an
equivalence on the quotient by the extended ideal. -/
@[stacks 07LX]
theorem exists_etale_unit_lift_of_quotient
    (I : Ideal A) {ubar : A ⧸ I} (hubar : IsUnit ubar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (u' : A'),
      IsUnit u' ∧
        eIso ubar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) u' := sorry

/-- The canonical proof of etale-local unit lifting may be chosen to use an away-localization of
a representative of the quotient unit. -/
theorem exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
    (I : Ideal A) {ubar : A ⧸ I} (hubar : IsUnit ubar) :
    ∃ (u : A)
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I]
        ((Localization.Away u) ⧸
          Ideal.map (algebraMap A (Localization.Away u)) I)),
      Ideal.Quotient.mk I u = ubar := sorry

end Algebra
