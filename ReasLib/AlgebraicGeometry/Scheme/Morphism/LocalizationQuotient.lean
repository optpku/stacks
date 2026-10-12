/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocalizationQuotientCoprod

noncomputable section

variable (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]

/-- The coproduct of the spectra of a ring localized at a prime and its quotient
by that prime. -/
def source : Scheme.{u} :=
  Spec (CommRingCat.of (Localization.AtPrime p)) ⨿ Spec (CommRingCat.of (A ⧸ p))

/-- The morphism from the localization-quotient coproduct to the spectrum of the
ring, induced by the localization and quotient ring maps. -/
def hom : source A p ⟶ Spec (CommRingCat.of A) :=
  coprod.desc
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime p))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p)))

variable [IsDomain A] [ValuationRing A]

/-- The localization-quotient coproduct morphism of a valuation ring at a prime
is universally submersive. -/
instance universallySubmersive : UniversallySubmersive (hom A p) := sorry

end

end AlgebraicGeometry.LocalizationQuotientCoprod
