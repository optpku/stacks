/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import ReasLib.RingTheory.AdicCompletion.LocalMap.Flat
public import ReasLib.RingTheory.AdicCompletion.LocalMap.Unramified
public import ReasLib.RingTheory.Etale.LocalRing

/-!
# Etale local maps on maximal-ideal completions

Completion invariance of essential etaleness and the resulting finite-free
description of the completed target.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AdicCompletion.LocalMap

/-- For an essentially finite type local homomorphism of Noetherian local rings,
essential etaleness is equivalent to essential etaleness, and to ordinary
etaleness, of the induced map on maximal-ideal completions. -/
theorem etale_tfae
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (h_essentiallyFiniteType : f.EssFiniteType) :
    List.TFAE [
      f.EssEtale,
      (AdicCompletion.mapLocal f).EssEtale,
      (AdicCompletion.mapLocal f).Etale] := sorry

/-- If an essentially finite type local homomorphism of Noetherian local rings
is essentially etale, then its completed target is linearly equivalent over
the completed source to a nonempty finite direct sum of copies of that source. -/
theorem exists_linearEquiv_of_essEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (h_essentiallyFiniteType : f.EssFiniteType)
    (hf : f.EssEtale) :
    -- Local instance justification (instance diamond): the action is induced by the explicit completion map for `f`; the same completions may admit other maps.
    letI : Algebra (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) :=
      AdicCompletion.mapLocalAlgebra f
    ∃ n : ℕ, 1 ≤ n ∧
      Nonempty
        (AdicCompletion (maximalIdeal B) B ≃ₗ[AdicCompletion (maximalIdeal A) A]
          Fin n →₀ AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion.LocalMap
