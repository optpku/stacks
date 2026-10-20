/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Lemma_60_17_5_Completion
public import stacks_project.Chap60.Lemma_60_17_5_Retract
public import stacks_project.Chap60.Remark_60_17_6_Lifting

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

/-- A finite polynomial presentation `A → P → C`, a factorization through an
algebra `P'` with the strong lifting property, and divided-power `A`-algebra
maps `a : D → D'`, `b : D' → D` compatible with the maps to `C` and satisfying
`a ∘ b = id_{D'}`. -/
structure LiftingRetract [Algebra.HasStrongLifting A P'] where
  /-- Number of polynomial generators of `P = A[y₁, …, yₙ]`. -/
  n : ℕ
  /-- The polynomial presentation map `P → C`. -/
  π : MvPolynomial (polynomialIndex n) A →ₐ[A] C
  /-- Surjectivity of the polynomial presentation. -/
  hπ : Function.Surjective π
  /-- Kernel ideal of the polynomial presentation. -/
  J : Ideal (MvPolynomial (polynomialIndex n) A)
  /-- Identification of `J` with the kernel of `π`. -/
  hJ : J = RingHom.ker π.toRingHom
  /-- Compatibility of `I` with the polynomial kernel. -/
  hIJ : Ideal.map (algebraMap A (MvPolynomial (polynomialIndex n) A)) I ≤ J
  /-- Divided-power envelope of the polynomial presentation. -/
  E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial (polynomialIndex n) A)) J hIJ
  /-- Universal property of the polynomial envelope. -/
  hE : DividedPowerEnvelope.IsUniversal γ
    (algebraMap A (MvPolynomial (polynomialIndex n) A)) hIJ E
  /-- Extended divided powers on the polynomial completion `D`. -/
  γbar : DividedPowers
    (Ideal.map (algebraMap E.D
      (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal)
  /-- Extended divided powers on the lifting completion `D'`. -/
  γbar' : DividedPowers
    (Ideal.map (algebraMap E'.D
      (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')) E'.D.ideal)
  /-- The polynomial completion structure extends the envelope divided powers. -/
  γbar_extends : E.D.dividedPowers.IsDPMorphism γbar
    (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE))
  /-- The lifting completion structure extends its envelope divided powers. -/
  γbar'_extends : E'.D.dividedPowers.IsDPMorphism γbar'
    (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'))
  /-- Factorization of the polynomial presentation through `P'`. -/
  toP : MvPolynomial (polynomialIndex n) A →ₐ[A] P'
  /-- The polynomial presentation is `P → P' → C`. -/
  toP_comp : π'.comp toP = π
  /-- The divided-power `A`-algebra map `a : D → D'`. -/
  a : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE →+*
    crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
  /-- The divided-power `A`-algebra map `b : D' → D`. -/
  b : crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' →+*
    crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE
  /-- The retract map `a` respects the given base algebra maps. -/
  a_base : a.comp (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) =
    crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
  /-- The retract map `b` respects the given base algebra maps. -/
  b_base : b.comp (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') =
    crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE
  /-- `a` is compatible with the structure maps to `C`. -/
  a_toC :
    (crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp a =
      crystallineDOf.toC p I γ π hπ J hJ hIC hpnil hIJ E hE
  /-- `b` is compatible with the structure maps to `C`. -/
  b_toC :
    (crystallineDOf.toC p I γ π hπ J hJ hIC hpnil hIJ E hE).comp b =
      crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
  /-- Retract identity `a ∘ b = id_{D'}`. -/
  retract_left : a.comp b = RingHom.id _
  /-- `a` is a morphism of divided-power algebras. -/
  a_isDP : γbar.IsDPMorphism γbar' a
  /-- `b` is a morphism of divided-power algebras. -/
  b_isDP : γbar'.IsDPMorphism γbar b

/-- Package a finite polynomial presentation, its factorization through `P'`,
and divided-power retract maps `a`, `b`, together with their required laws. -/
noncomputable def LiftingRetract.of
    [Algebra.HasStrongLifting A P']
    {n : ℕ} (π : MvPolynomial (polynomialIndex n) A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (polynomialIndex n) A))
    (hJ : J = RingHom.ker π.toRingHom)
    (hIJ : Ideal.map (algebraMap A (MvPolynomial (polynomialIndex n) A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial (polynomialIndex n) A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial (polynomialIndex n) A)) hIJ E)
    (γbar : DividedPowers
      (Ideal.map (algebraMap E.D
        (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal))
    (γbar' : DividedPowers
      (Ideal.map (algebraMap E'.D
        (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')) E'.D.ideal))
    (toP : MvPolynomial (polynomialIndex n) A →ₐ[A] P')
    (a : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE →+*
      crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (b : crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' →+*
      crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (hγbar : E.D.dividedPowers.IsDPMorphism γbar
      (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)))
    (hγbar' : E'.D.dividedPowers.IsDPMorphism γbar'
      (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')))
    (htoP : π'.comp toP = π)
    (haBase : a.comp (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) =
      crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (hbBase : b.comp (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') =
      crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (haToC : (crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp a =
      crystallineDOf.toC p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (hbToC : (crystallineDOf.toC p I γ π hπ J hJ hIC hpnil hIJ E hE).comp b =
      crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (hRetract : a.comp b = RingHom.id _)
    (haDP : γbar.IsDPMorphism γbar' a) (hbDP : γbar'.IsDPMorphism γbar b) :
    LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  { n := n
    π := π
    hπ := hπ
    J := J
    hJ := hJ
    hIJ := hIJ
    E := E
    hE := hE
    γbar := γbar
    γbar' := γbar'
    γbar_extends := hγbar
    γbar'_extends := hγbar'
    toP := toP
    toP_comp := htoP
    a := a
    b := b
    a_base := haBase
    b_base := hbBase
    a_toC := haToC
    b_toC := hbToC
    retract_left := hRetract
    a_isDP := haDP
    b_isDP := hbDP }

/-- A lifting retract is compatible with the maps to `C`, satisfies `a ∘ b = id`,
and both maps are divided-power morphisms. -/
theorem LiftingRetract.spec
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    (crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp R.a =
        crystallineDOf.toC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE ∧
      (crystallineDOf.toC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE).comp R.b =
        crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' ∧
      R.a.comp R.b = RingHom.id _ ∧
      R.γbar.IsDPMorphism R.γbar' R.a ∧
      R.γbar'.IsDPMorphism R.γbar R.b :=
  sorry

/-- Convert a smooth polynomial retract into a lifting retract via
`HasStrongLifting.ofSmooth`. -/
noncomputable def LiftingRetract.ofSmooth
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  LiftingRetract.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
    R.π R.hπ R.J R.hJ R.hIJ R.E R.hE R.γbar R.γbar' R.toP' R.a R.b
    R.γbar_extends R.γbar'_extends R.toP'_comp R.a_base R.b_base
    R.a_toC R.b_toC R.retract_left R.a_isDP R.b_isDP

/-- Polynomial completed envelope `D` of a lifting retract presentation. -/
abbrev LiftingRetract.polyD
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE

/-- The polynomial completion of a lifting retract is `crystallineD` of its
presentation. -/
theorem LiftingRetract.polyD_eq
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.polyD =
      crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE :=
  sorry

/-- Completed envelope `D'` associated to a lifting presentation. -/
abbrev LiftingRetract.liftingD
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

/-- The lifting completion of a retract is `crystallineDOf` of `P'`. -/
theorem LiftingRetract.liftingD_eq
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.liftingD =
      crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  sorry

/-- The polynomial completion `D` is an `A`-algebra via `crystallineDBaseMap`. -/
noncomputable instance LiftingRetract.algebraPoly
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    Algebra A R.polyD :=
  crystallineD.algebra p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE

/-- The lifting completion `D'` is an `A`-algebra via `crystallineDOfBaseMap`. -/
noncomputable instance LiftingRetract.algebraLifting
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    Algebra A R.liftingD :=
  crystallineDOf.algebra p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

/-- The retract map `a` as an `A`-algebra homomorphism `D →ₐ[A] D'`. -/
noncomputable def LiftingRetract.aAlgHom
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.polyD →ₐ[A] R.liftingD :=
  { __ := R.a
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.a_base }

/-- The retract map `b` as an `A`-algebra homomorphism `D' →ₐ[A] D`. -/
noncomputable def LiftingRetract.bAlgHom
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.liftingD →ₐ[A] R.polyD :=
  { __ := R.b
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.b_base }

/-- `aAlgHom` forgets to the stored ring map `a`. -/
theorem LiftingRetract.aAlgHom_toRingHom
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.aAlgHom.toRingHom = R.a :=
  sorry

/-- `bAlgHom` forgets to the stored ring map `b`. -/
theorem LiftingRetract.bAlgHom_toRingHom
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.bAlgHom.toRingHom = R.b :=
  sorry

/-- Completed divided-power differentials of the polynomial envelope `D`. -/
abbrev LiftingRetract.omegaPoly
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineOmegaD
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p

/-- Unfolding of the polynomial completed differentials of a lifting retract. -/
theorem LiftingRetract.omegaPoly_eq
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaPoly =
      crystallineOmegaD
        (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p :=
  sorry

/-- Completed divided-power differentials of the lifting envelope `D'`. -/
abbrev LiftingRetract.omegaLifting
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineOmegaD
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p

/-- Unfolding of the lifting completed differentials of a retract. -/
theorem LiftingRetract.omegaLifting_eq
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaLifting =
      crystallineOmegaD
        (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p :=
  sorry

/-- The Remark 60.6.9 comparison `φ : Ω_D → Ω_{D'}` induced by `a`. -/
noncomputable def LiftingRetract.formsA
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaPoly →+ R.omegaLifting :=
  formsOfHom p
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.a R.a_base R.a_isDP

/-- The Remark 60.6.9 comparison `Ω_{D'} → Ω_D` induced by `b`. -/
noncomputable def LiftingRetract.formsB
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaLifting →+ R.omegaPoly :=
  formsOfHom p
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.b R.b_base R.b_isDP

/-- `formsA` is linear over `a`. -/
theorem LiftingRetract.formsA_smul
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.polyD) (ω : R.omegaPoly) :
    (R.formsA) (r • ω) = R.a r • (R.formsA) ω :=
  sorry

/-- `formsA` intertwines the universal derivations with `a`. -/
theorem LiftingRetract.formsA_der
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.polyD) :
    (R.formsA)
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p r) =
      crystallineOmegaD_derivation
        (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p (R.a r) :=
  sorry

/-- `formsB` is linear over `b`. -/
theorem LiftingRetract.formsB_smul
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.liftingD) (ω : R.omegaLifting) :
    (R.formsB) (r • ω) = R.b r • (R.formsB) ω :=
  sorry

/-- `formsB` intertwines the universal derivations with `b`. -/
theorem LiftingRetract.formsB_der
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.liftingD) :
    (R.formsB)
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p r) =
      crystallineOmegaD_derivation
        (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p (R.b r) :=
  sorry

/-- Because `a ∘ b = id_{D'}`, the induced form maps satisfy `formsA ∘ formsB = id`. -/
theorem LiftingRetract.formsA_comp_formsB
    [Algebra.HasStrongLifting A P']
    (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.formsA.comp R.formsB = AddMonoidHom.id _ :=
  sorry

/-- In Situation 60.5.1, if `A → P'` has the strong lifting property and
`P' → C` is surjective with kernel `J'`, then the `p`-adic completion `D'` of
`D_{P',γ}(J')` admits a polynomial retract as in Lemma 60.17.5. -/
theorem exists_liftingRetract [Algebra.HasStrongLifting A P'] :
    Nonempty
      (LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :=
  sorry

end CrystallineConnectionPair

end
