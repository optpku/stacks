module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.DividedPowers.Category
public import ReasLib.RingTheory.Ideal.Principal
public import stacks_project.Chap60.«60_2_2_1_Envelope»
public import stacks_project.Chap60.«60_17_0_1»
public import stacks_project.Chap60.«60_17_0_4_TensorPower»
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

universe u

/-- The `p`-adic completion of the divided-power envelope attached
to the `(n + 1)`-fold tensor-power stage `tensorPowerCarrier A ι n` and its kernel ideal, representing
the inverse limit of the quotients by powers of `p`, under the localization,
vanishing, nilpotence, and universal-envelope hypotheses of Situation 60.5.1. -/
noncomputable abbrev crystallineDn
    {A : Type u} [CommRing A]
    (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ
      (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (tensorPowerCarrier A ι n)) hIJ E) : Type u :=
  principalAdicCompletion (p : E.D)

section CrystallineSetup

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
  [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
  (I : Ideal A) (γ : DividedPowers I)
  {C : Type u} [CommRing C] [Algebra A C]
  {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
  (hπ : Function.Surjective π) (n : ℕ)
  (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
  (hpnil : IsNilpotent (p : C))
  (J : Ideal (tensorPowerCarrier A ι n))
  (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
  (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
  (E : DividedPowerEnvelope I γ
    (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
  (hE : DividedPowerEnvelope.IsUniversal γ
    (algebraMap A (tensorPowerCarrier A ι n)) hIJ E)

/- 60.17.0.4 -/
@[stacks 07JF] #check (principalAdicCompletion (p : E.D) : Type u)

end CrystallineSetup
