/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.BaseChange
public import stacks_project.Chap60.Lemma_60_17_3_Pair
public import stacks_project.Chap60.Lemma_60_17_5_Completion

@[expose] public section

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')

namespace CrystallineConnectionPair

/-- A finite polynomial index in the coefficient universe. -/
abbrev polynomialIndex (n : ℕ) : Type u := DividedPowerEnvelope.polynomialIndex n

/-- A finite polynomial completed-envelope retract of a smooth presentation. -/
abbrev DividedPowerRetract [Algebra.Smooth A P'] :=
  DividedPowerEnvelope.PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

/-- The completed differential homomorphism induced by a compatible divided-power homomorphism. -/
noncomputable def formsOfHom
    {D D' : Type u} [CommRing D] [CommRing D']
    (fD : A →+* D) (fD' : A →+* D')
    {JD : Ideal D} {JD' : Ideal D'}
    (γD : DividedPowers JD) (γD' : DividedPowers JD')
    (φ : D →+* D') (hA : φ.comp fD = fD')
    (hDP : γD.IsDPMorphism γD' φ) :
    crystallineOmegaD fD γD p →+ crystallineOmegaD fD' γD' p :=
  Connection.Adic.completedFormsMap fD fD' γD γD' φ hA hDP p

end CrystallineConnectionPair

end
