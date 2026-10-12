/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import ReasLib.RingTheory.Etale.Essential

@[expose] public section

universe u v

namespace RingHom.EssEtale

/-- An essentially étale local homomorphism of local rings factors through a
standard étale algebra and a localization at a prime. -/
theorem exists_standardEtale_localizationAtPrime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} [IsLocalHom φ]
    (hφ : φ.EssEtale) :
    ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (_ : q.IsPrime)
      (ψ : P.Ring →+* B),
      q.primeCompl.IsLocalizationMap ψ ∧
        φ = ψ.comp (algebraMap A P.Ring) := sorry

end RingHom.EssEtale

namespace Algebra

/-- A finitely presented commutative algebra is étale at a prime if and only if
some principal localization away from that prime is standard étale. -/
theorem isEtaleAt_iff_exists_isStandardEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [FinitePresentation A B] (q : Ideal B) [q.IsPrime] :
    IsEtaleAt A q ↔
      ∃ g : B, g ∉ q ∧ IsStandardEtale A (Localization.Away g) := sorry

end Algebra
