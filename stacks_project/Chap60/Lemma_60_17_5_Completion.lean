/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic
public import stacks_project.Chap60.«60_17_0_1»

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

/-- The `p`-adic completion of a relative divided-power envelope `D_{P',γ}(J')`. -/
noncomputable abbrev crystallineDOf
    (π' : P' →ₐ[A] C) (hπ' : Function.Surjective π')
    (J' : Ideal P') (hJ' : J' = RingHom.ker π'.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
    (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
    (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E') : Type u :=
  AdicCompletion (Ideal.span {(p : E'.D)}) E'.D

/-- The general envelope completion unfolds to adic completion of `E'.D`. -/
theorem crystallineDOf_eq_adicCompletion :
    crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' =
      AdicCompletion (Ideal.span {(p : E'.D)}) E'.D :=
  sorry

/-- The canonical ring map from `A` into `D'`. -/
noncomputable def crystallineDOfBaseMap :
    A →+* crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')).comp
    (E'.toD.comp (algebraMap A P'))

/-- The `A`-algebra structure on `D'`. -/
noncomputable instance crystallineDOf.algebra :
    Algebra A (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :=
  (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').toAlgebra

/-- Unfolding of the base map into `D'`. -/
theorem crystallineDOfBaseMap_comp :
    crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' =
      (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')).comp
        (E'.toD.comp (algebraMap A P')) :=
  sorry

/-- Identification of `P' ⧸ J'` with `C` along the given surjection. -/
noncomputable def crystallineDOf.quotientEquiv :
    (P' ⧸ J') ≃+* C :=
  (Ideal.quotEquivOfEq hJ').trans (π'.toRingHom.quotientKerEquivOfSurjective hπ')

/-- The structure map `D' → C` of the completed envelope. -/
noncomputable def crystallineDOf.toC :
    crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' →+* C :=
  (Ideal.Quotient.lift (Ideal.span {(p : E'.D)} ^ hpnil.choose)
      ((crystallineDOf.quotientEquiv π' hπ' J' hJ').toRingHom.comp E'.toQuotient)
      sorry).comp
    (AdicCompletion.evalₐ (Ideal.span {(p : E'.D)}) hpnil.choose).toRingHom

/-- `D' → C` extends the envelope quotient `E'.D → P' ⧸ J' ≃+* C` along
`AdicCompletion.of`. -/
theorem crystallineDOf.toC_comp :
    (crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :
        crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' → C) ∘
      AdicCompletion.of (Ideal.span {(p : E'.D)}) E'.D =
    ((crystallineDOf.quotientEquiv π' hπ' J' hJ').toRingHom.comp E'.toQuotient :
        E'.D → C) :=
  sorry

/-- The polynomial completed envelope is the special case of `crystallineDOf`. -/
theorem crystallineD_eq_crystallineDOf
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A))
    (hJ : J = RingHom.ker π.toRingHom)
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial ι A)) hIJ E) :
    crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE =
      crystallineDOf p I γ π hπ J hJ hIC hpnil hIJ E hE :=
  sorry

end
