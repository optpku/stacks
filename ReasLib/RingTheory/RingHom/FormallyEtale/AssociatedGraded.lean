/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.RingTheory.RingHom.FormallyEtale.QuotientPow
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Associated graded rings under formally etale maps

This leaf owns the associated-graded comparison induced by a formally etale
ring map that is surjective modulo an ideal.  It is stated directly with the
canonical `Ideal.AssociatedGraded` owners and the source ideal
`Ideal.comap f J`, so downstream applications do not need a chapter-specific
quotient-Rees presentation.
@stack 0H1D
-/

universe u v

namespace RingHom.FormallyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.150.6, degreewise form: a formally etale map whose reduction
modulo `J` is surjective induces a bijection on the degree-`n` associated
graded pieces. -/
@[stacks 0H1D "formally etale associated graded degree maps"]
theorem associatedGradedGrade_bijective
    (f : R →+* S) (J : Ideal S)
    (h_etale : f.FormallyEtale)
    (h_surj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    Function.Bijective
      (Ideal.AssociatedGraded.mapGrade (Ideal.comap f J) J f le_rfl n) := sorry

/-- Lemma 10.150.6: a formally etale map whose reduction modulo `J` is
surjective induces a bijection on the associated graded rings. -/
@[stacks 0H1D "formally etale associated graded ring maps"]
theorem associatedGradedMap_bijective
    (f : R →+* S) (J : Ideal S)
    (h_etale : f.FormallyEtale)
    (h_surj : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Bijective
      ((Ideal.AssociatedGraded.map f le_rfl) :
        Ideal.AssociatedGraded.ring (Ideal.comap f J) →+*
          Ideal.AssociatedGraded.ring J) := sorry

end RingHom.FormallyEtale
