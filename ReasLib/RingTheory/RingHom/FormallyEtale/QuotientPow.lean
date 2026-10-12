/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Formally étale maps and powers of quotient ideals

This leaf owns the map-first quotient statement.  The source ideal is
`J.comap f`; the compatibility proof is generated canonically by
`Ideal.le_comap_pow`, so callers do not need a separately named comap-power
object.
@stack 0H1D
-/

universe u v

namespace RingHom.FormallyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.150.6 (Stacks tag `0H1D`): a formally étale map whose reduction modulo `J` is
surjective induces bijections on all powers of the quotient map. -/
@[stacks 0H1D "formally étale quotient maps on ideal powers"]
theorem quotientMap_pow_bijective
    (f : R →+* S) (J : Ideal S)
    (h_etale : f.FormallyEtale)
    (h_surj : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (n : ℕ) :
    Function.Bijective
      ((Ideal.quotientMap (J ^ n) f (J.le_comap_pow f n)) :
        R ⧸ ((Ideal.comap f J) ^ n) →+* S ⧸ (J ^ n)) := sorry

end RingHom.FormallyEtale
