/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Smooth
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

/-- The canonical ring map from `A` into `D'`. -/
noncomputable def crystallineDOfBaseMap :
    A →+* crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')).comp
    (E'.toD.comp (algebraMap A P'))

/-- The `A`-algebra structure on `D'`. -/
@[implicit_reducible] noncomputable instance crystallineDOf.algebra :
    Algebra A (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :=
  (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').toAlgebra

/-- The canonical quotient from the completed smooth envelope to its presented algebra. -/
noncomputable def crystallineDOf.toC :
    crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' →+* C :=
  DividedPowerEnvelope.completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

end
