module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Maps
public import ReasLib.RingTheory.KrullDimension.QuasiFinite

@[expose] public section

/-!
# Local Krull dimension for etale maps

@stack 07QP

This leaf specializes the faithfully-flat and quasi-finite comparison API to
an etale algebra map.
-/

universe u v

namespace Algebra.Etale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.Etale A B]

/-- An etale map preserves the Krull dimension of localizations at a prime and its
contraction. -/
@[stacks 07QP "etale local Krull-dimension invariance"]
theorem ringKrullDim_localizationAtPrime_eq
    (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime (q.under A)) =
      ringKrullDim (Localization.AtPrime q) := sorry

end Algebra.Etale

namespace RingHom.Etale

/-- A local étale homomorphism between Noetherian local rings preserves Krull dimension. -/
@[stacks 039S]
theorem ringKrullDim_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    ringKrullDim A = ringKrullDim B := sorry

end RingHom.Etale
