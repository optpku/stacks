/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.AdicCompletion
import StacksCheckRecall
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.«60_2_2_1_Envelope»
public import stacks_project.Chap60.«60_17_0_1_Universal»
public import ReasLib.RingTheory.Ideal.Principal

@[expose] public section

universe u

/-- The ring `D` is the `p`-adic completion of the divided-power
envelope `D_Pγ_J` for the polynomial presentation `MvPolynomial ι A`,
under the hypotheses of Situation 60.5.1 and the universal mapping property of
the envelope, represented by the compatible inverse-limit carrier
`AdicCompletion (Ideal.span {(p : E.D)}) E.D`. -/
noncomputable abbrev crystallineD
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A))
    (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial ι A)) hIJ E) : Type u :=
  principalAdicCompletion (p : E.D)

section CrystallineSetup

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
  [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
  (I : Ideal A) (γ : DividedPowers I)
  {C : Type u} [CommRing C] [Algebra A C]
  {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
  (hπ : Function.Surjective π)
  (J : Ideal (MvPolynomial ι A))
  (hJ : J = RingHom.ker π.toRingHom)
  (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
  (hpnil : IsNilpotent (p : C))
  (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
  (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
  (hE : DividedPowerEnvelope.IsUniversal γ
    (algebraMap A (MvPolynomial ι A)) hIJ E)

/- 60.17.0.1 -/
@[stacks 07J8] #check (principalAdicCompletion (p : E.D) : Type u)

end CrystallineSetup
