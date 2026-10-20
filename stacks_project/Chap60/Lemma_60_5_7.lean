/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.WeaklyInitial
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 60.5.7: the completed divided-power envelope of a polynomial
presentation admits a morphism to every completed crystalline object. -/
@[stacks 07KI] #check (DividedPowerEnvelope.nonempty_completedCrisHom :
  ∀ (p : ℕ) [Fact (Nat.Prime p)]
    {A C : Type u} [CommRing A] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A C] {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial ι A)) hIJ E)
    (T : CompletedCrisObject p A I γ C (algebraMap A C) hIC h_pC),
    Nonempty (CompletedCris.Hom γ (algebraMap A C) hIC h_pC
      (DividedPowerEnvelope.polynomialCompletedCrisObject p γ π hπ hIC h_pC hJ E hE) T))
