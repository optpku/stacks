/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import ReasLib.RingTheory.AdicCompletion.Quotient.Ideal
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

set_option backward.privateInPublic true

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

namespace DividedPowerEnvelope

/-- The canonical completion bound supplied by the crystalline envelope construction. -/
private noncomputable def completionBound : ℕ :=
  (DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P' I γ C (algebraMap A C)
    π'.toRingHom π'.comp_algebraMap hIC J' hJ' hπ' hpnil E' hE').choose

/-- The canonical bound puts a power of the adic ideal in the envelope ideal. -/
private noncomputable def completionContainment :
    Ideal.span {(p : E'.D)} ^ completionBound p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' ≤ E'.D.ideal :=
  (DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P' I γ C (algebraMap A C)
    π'.toRingHom π'.comp_algebraMap hIC J' hJ' hπ' hpnil E' hE').choose_spec.2.choose

/-- The quotient homomorphism from the completed universal envelope to the presented algebra. -/
noncomputable def completedToC : AdicCompletion (Ideal.span {(p : E'.D)}) E'.D →+* C :=
  DividedPowers.PAdic.envelopeCompletionToC p π'.toRingHom hπ' hJ' E' hE'
    (completionBound p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (completionContainment p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (DividedPowers.PAdic.envelopeCompletionDividedPowers E' _ _)

/-- The completed envelope quotient extends the canonical quotient of the original envelope. -/
theorem completedToC_comp :
    (completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp
        (algebraMap E'.D (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)) =
      DividedPowers.PAdic.envelopeToC π'.toRingHom hπ' hJ' E' hE' := sorry

/-- The coefficient homomorphism into a completed relative envelope. -/
noncomputable def completedBaseMap : A →+* AdicCompletion (Ideal.span {(p : E'.D)}) E'.D :=
  (algebraMap E'.D (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)).comp
    (E'.toD.comp (algebraMap A P'))

/-- Universe-lifted finite index of a polynomial presentation `A[y₁, …, yₙ]`,
with its index in the coefficient universe. -/
abbrev polynomialIndex (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- A finite polynomial presentation `A → P → C`, a factorization through the
smooth algebra `P'`, and divided-power `A`-algebra maps `a : D → D'`,
`b : D' → D` compatible with the maps to `C` and satisfying `a ∘ b = id_{D'}`. -/
structure PolynomialRetract [Algebra.Smooth A P'] where
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
      (AdicCompletion (Ideal.span {(p : E.D)}) E.D)) E.D.ideal)
  /-- Extended divided powers on the smooth completion `D'`. -/
  γbar' : DividedPowers
    (Ideal.map (algebraMap E'.D
      (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)) E'.D.ideal)
  /-- The polynomial completion structure extends the envelope divided powers. -/
  γbar_extends : E.D.dividedPowers.IsDPMorphism γbar
    (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))
  /-- The smooth completion structure extends its envelope divided powers. -/
  γbar'_extends : E'.D.dividedPowers.IsDPMorphism γbar'
    (algebraMap E'.D (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D))
  /-- Factorization of the polynomial presentation through `P'`. -/
  toP' : MvPolynomial (polynomialIndex n) A →ₐ[A] P'
  /-- The polynomial presentation is `P → P' → C`. -/
  toP'_comp : π'.comp toP' = π
  /-- The divided-power `A`-algebra map `a : D → D'`. -/
  a : AdicCompletion (Ideal.span {(p : E.D)}) E.D →+*
    AdicCompletion (Ideal.span {(p : E'.D)}) E'.D
  /-- The divided-power `A`-algebra map `b : D' → D`. -/
  b : AdicCompletion (Ideal.span {(p : E'.D)}) E'.D →+*
    AdicCompletion (Ideal.span {(p : E.D)}) E.D
  /-- The retract map `a` respects the given base algebra maps. -/
  a_base : a.comp (completedBaseMap p I γ J hIJ E) =
    completedBaseMap p I γ J' hIJ' E'
  /-- The retract map `b` respects the given base algebra maps. -/
  b_base : b.comp (completedBaseMap p I γ J' hIJ' E') =
    completedBaseMap p I γ J hIJ E
  /-- `a` is compatible with the structure maps to `C`. -/
  a_toC :
    (completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp a =
      completedToC p I γ π hπ J hJ hIC hpnil hIJ E hE
  /-- `b` is compatible with the structure maps to `C`. -/
  b_toC :
    (completedToC p I γ π hπ J hJ hIC hpnil hIJ E hE).comp b =
      completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
  /-- Retract identity `a ∘ b = id_{D'}`. -/
  retract_left : a.comp b = RingHom.id _
  /-- `a` is a morphism of divided-power algebras. -/
  a_isDP : γbar.IsDPMorphism γbar' a
  /-- `b` is a morphism of divided-power algebras. -/
  b_isDP : γbar'.IsDPMorphism γbar b

/-- Package a finite polynomial presentation, its factorization through `P'`,
and divided-power retract maps `a`, `b`, together with their required laws. -/
noncomputable def PolynomialRetract.of
    [Algebra.Smooth A P']
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
        (AdicCompletion (Ideal.span {(p : E.D)}) E.D)) E.D.ideal))
    (γbar' : DividedPowers
      (Ideal.map (algebraMap E'.D
        (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)) E'.D.ideal))
    (toP' : MvPolynomial (polynomialIndex n) A →ₐ[A] P')
    (a : AdicCompletion (Ideal.span {(p : E.D)}) E.D →+*
      AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)
    (b : AdicCompletion (Ideal.span {(p : E'.D)}) E'.D →+*
      AdicCompletion (Ideal.span {(p : E.D)}) E.D)
    (hγbar : E.D.dividedPowers.IsDPMorphism γbar
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (hγbar' : E'.D.dividedPowers.IsDPMorphism γbar'
      (algebraMap E'.D (AdicCompletion (Ideal.span {(p : E'.D)}) E'.D)))
    (htoP : π'.comp toP' = π)
    (haBase : a.comp (completedBaseMap p I γ J hIJ E) =
      completedBaseMap p I γ J' hIJ' E')
    (hbBase : b.comp (completedBaseMap p I γ J' hIJ' E') =
      completedBaseMap p I γ J hIJ E)
    (haToC : (completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp a =
      completedToC p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (hbToC : (completedToC p I γ π hπ J hJ hIC hpnil hIJ E hE).comp b =
      completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (hRetract : a.comp b = RingHom.id _)
    (haDP : γbar.IsDPMorphism γbar' a) (hbDP : γbar'.IsDPMorphism γbar b) :
    PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
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
    toP' := toP'
    toP'_comp := htoP
    a := a
    b := b
    a_base := haBase
    b_base := hbBase
    a_toC := haToC
    b_toC := hbToC
    retract_left := hRetract
    a_isDP := haDP
    b_isDP := hbDP }

/-- A retract is compatible with the maps to `C`, satisfies `a ∘ b = id`, and
both maps are divided-power morphisms. -/
theorem PolynomialRetract.spec
    [Algebra.Smooth A P']
    (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    (completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp R.a =
        completedToC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE ∧
      (completedToC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE).comp R.b =
        completedToC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' ∧
      R.a.comp R.b = RingHom.id _ ∧
      R.γbar.IsDPMorphism R.γbar' R.a ∧
      R.γbar'.IsDPMorphism R.γbar R.b := sorry


/-- Polynomial completed envelope `D` of a retract presentation. -/
abbrev PolynomialRetract.polyD
    [Algebra.Smooth A P']
    (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  AdicCompletion (Ideal.span {(p : R.E.D)}) R.E.D

/-- Smooth completed envelope `D'` associated to a retract. -/
abbrev PolynomialRetract.smoothD
    [Algebra.Smooth A P']
    (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  AdicCompletion (Ideal.span {(p : E'.D)}) E'.D

/-- The retract map bundled over the coefficient actions selected by the two envelopes. -/
noncomputable def PolynomialRetract.aAlgHom
    [Algebra.Smooth A P']
    (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
  -- Local instance justification (noncanonical choice): the polynomial envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ R.J R.hIJ R.E).toAlgebra
  -- Local instance justification (noncanonical choice): the smooth envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ J' hIJ' E').toAlgebra
  R.polyD →ₐ[A] R.smoothD :=
  -- Local instance justification (noncanonical choice): the polynomial envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ R.J R.hIJ R.E).toAlgebra
  -- Local instance justification (noncanonical choice): the smooth envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ J' hIJ' E').toAlgebra
  { __ := R.a
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.a_base }

/-- The section map bundled over the coefficient actions selected by the two envelopes. -/
noncomputable def PolynomialRetract.bAlgHom
    [Algebra.Smooth A P']
    (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
  -- Local instance justification (noncanonical choice): the polynomial envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ R.J R.hIJ R.E).toAlgebra
  -- Local instance justification (noncanonical choice): the smooth envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ J' hIJ' E').toAlgebra
  R.smoothD →ₐ[A] R.polyD :=
  -- Local instance justification (noncanonical choice): the polynomial envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ R.J R.hIJ R.E).toAlgebra
  -- Local instance justification (noncanonical choice): the smooth envelope action is selected by its explicit structural map.
  letI := (completedBaseMap p I γ J' hIJ' E').toAlgebra
  { __ := R.b
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.b_base }

/-- A smooth surjective presentation admits a finite polynomial completed-envelope retract. -/
theorem PolynomialRetract.exists [Algebra.Smooth A P'] :
    Nonempty (PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') := sorry

end DividedPowerEnvelope
