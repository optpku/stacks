module

public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import ReasLib.RingTheory.DividedPowers.Envelope.AdicCompletion
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

open DividedPowers

universe u

namespace DividedPowerEnvelope

/-- The canonical completed crystalline object of a universal divided-power
envelope of a surjective polynomial presentation. -/
noncomputable def polynomialCompletedCrisObject
    (p : ℕ) [Fact (Nat.Prime p)]
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
    (hE : IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E) :
    CompletedCrisObject p A I γ C (algebraMap A C) hIC h_pC :=
  let N := nilpotencyClass (p : C)
  let hN := primePowLeIdeal γ (algebraMap A (MvPolynomial ι A)) hIJ
    E π.toRingHom hJ p h_pC
  PAdic.envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
    π.comp_algebraMap hIC h_pC hJ E hE N hN
    (PAdic.envelopeCompletionDividedPowers E N hN)
    (PAdic.envelopeCompletionDividedPowers_isDPMorphism E N hN)

/-- The underlying divided-power ring of the completed polynomial envelope is
its canonical adic completion, with the completed ideal and divided powers. -/
theorem polynomialCompletedCrisObject_B
    (p : ℕ) [Fact (Nat.Prime p)]
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
    (hE : IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E) :
    let N := nilpotencyClass (p : C)
    let hN := primePowLeIdeal γ (algebraMap A (MvPolynomial ι A)) hIJ
      E π.toRingHom hJ p h_pC
    (polynomialCompletedCrisObject p γ π hπ hIC h_pC hJ E hE).B =
      PAdic.envelopeCompletionRing p A (MvPolynomial ι A) I γ J hIJ E N hN
        (PAdic.envelopeCompletionDividedPowers E N hN) := sorry

/-- The base map of the completed polynomial envelope is the completion of its
base map, and its quotient map restricts to the original polynomial presentation. -/
theorem polynomialCompletedCrisObject_spec
    (p : ℕ) [Fact (Nat.Prime p)]
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
    (hE : IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E) :
    let N := nilpotencyClass (p : C)
    let hN := primePowLeIdeal γ (algebraMap A (MvPolynomial ι A)) hIJ
      E π.toRingHom hJ p h_pC
    let completionMap := PAdic.envelopeCompletionMap p A (MvPolynomial ι A) I γ J hIJ
      E N hN (PAdic.envelopeCompletionDividedPowers E N hN)
    let D := polynomialCompletedCrisObject p γ π hπ hIC h_pC hJ E hE
    D.base.toRingHom = completionMap.comp E.base.toRingHom ∧
      D.toC.comp (completionMap.comp E.toD) = π.toRingHom := sorry

/-- The completed universal divided-power envelope of a surjective polynomial
presentation admits a morphism to every completed crystalline object over the
same base and target. -/
theorem nonempty_completedCrisHom
    (p : ℕ) [Fact (Nat.Prime p)]
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
    (hE : IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (T : CompletedCrisObject p A I γ C (algebraMap A C) hIC h_pC) :
    Nonempty (CompletedCris.Hom γ (algebraMap A C) hIC h_pC
      (polynomialCompletedCrisObject p γ π hπ hIC h_pC hJ E hE) T) := sorry

end DividedPowerEnvelope
