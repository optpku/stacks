module

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

/-- Universe-lifted finite index of a polynomial presentation `A[y₁, …, yₙ]`,
so that `crystallineD` can take the index in `Type u`. -/
abbrev polynomialIndex (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- The polynomial index unfolds to the universe lift of `Fin n`. -/
theorem polynomialIndex_eq (n : ℕ) :
    polynomialIndex n = ULift.{u} (Fin n) :=
  sorry

/-- A finite polynomial presentation `A → P → C`, a factorization through the
smooth algebra `P'`, and divided-power `A`-algebra maps `a : D → D'`,
`b : D' → D` compatible with the maps to `C` and satisfying `a ∘ b = id_{D'}`. -/
structure DividedPowerRetract [Algebra.Smooth A P'] where
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
  /-- Extended divided powers on the smooth completion `D'`. -/
  γbar' : DividedPowers
    (Ideal.map (algebraMap E'.D
      (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')) E'.D.ideal)
  /-- The polynomial completion structure extends the envelope divided powers. -/
  γbar_extends : E.D.dividedPowers.IsDPMorphism γbar
    (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE))
  /-- The smooth completion structure extends its envelope divided powers. -/
  γbar'_extends : E'.D.dividedPowers.IsDPMorphism γbar'
    (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'))
  /-- Factorization of the polynomial presentation through `P'`. -/
  toP' : MvPolynomial (polynomialIndex n) A →ₐ[A] P'
  /-- The polynomial presentation is `P → P' → C`. -/
  toP'_comp : π'.comp toP' = π
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
and divided-power retract maps `a`, `b`, together with their required laws.
Arbitrary maps cannot be promoted to retracts by deferred false obligations. -/
noncomputable def DividedPowerRetract.of
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
        (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal))
    (γbar' : DividedPowers
      (Ideal.map (algebraMap E'.D
        (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')) E'.D.ideal))
    (toP' : MvPolynomial (polynomialIndex n) A →ₐ[A] P')
    (a : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE →+*
      crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (b : crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' →+*
      crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (hγbar : E.D.dividedPowers.IsDPMorphism γbar
      (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)))
    (hγbar' : E'.D.dividedPowers.IsDPMorphism γbar'
      (algebraMap E'.D (crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')))
    (htoP : π'.comp toP' = π)
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
    DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
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
theorem DividedPowerRetract.spec
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    (crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE').comp R.a =
        crystallineDOf.toC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE ∧
      (crystallineDOf.toC p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE).comp R.b =
        crystallineDOf.toC p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' ∧
      R.a.comp R.b = RingHom.id _ ∧
      R.γbar.IsDPMorphism R.γbar' R.a ∧
      R.γbar'.IsDPMorphism R.γbar R.b :=
  sorry


/-- Polynomial completed envelope `D` of a retract presentation. -/
abbrev DividedPowerRetract.polyD
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE

/-- The polynomial completion of a retract is `crystallineD` of its presentation. -/
theorem DividedPowerRetract.polyD_eq
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.polyD =
      crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE :=
  sorry

/-- Smooth completed envelope `D'` associated to a retract. -/
abbrev DividedPowerRetract.smoothD
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

/-- The smooth completion of a retract is `crystallineDOf` of `P'`. -/
theorem DividedPowerRetract.smoothD_eq
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.smoothD =
      crystallineDOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :=
  sorry

/-- The polynomial completion `D` is an `A`-algebra via `crystallineDBaseMap`. -/
noncomputable instance DividedPowerRetract.algebraPoly
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    Algebra A R.polyD :=
  crystallineD.algebra p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE

/-- The smooth completion `D'` is an `A`-algebra via `crystallineDOfBaseMap`. -/
noncomputable instance DividedPowerRetract.algebraSmooth
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    Algebra A R.smoothD :=
  crystallineDOf.algebra p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'

/-- The retract map `a` as an `A`-algebra homomorphism `D →ₐ[A] D'`. -/
noncomputable def DividedPowerRetract.aAlgHom
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.polyD →ₐ[A] R.smoothD :=
  { __ := R.a
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.a_base }

/-- The retract map `b` as an `A`-algebra homomorphism `D' →ₐ[A] D`. -/
noncomputable def DividedPowerRetract.bAlgHom
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.smoothD →ₐ[A] R.polyD :=
  { __ := R.b
    commutes' := fun r ↦ congrArg (fun f ↦ f r) R.b_base }

/-- `aAlgHom` forgets to the stored ring map `a`. -/
theorem DividedPowerRetract.aAlgHom_toRingHom
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.aAlgHom.toRingHom = R.a :=
  sorry

/-- `bAlgHom` forgets to the stored ring map `b`. -/
theorem DividedPowerRetract.bAlgHom_toRingHom
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.bAlgHom.toRingHom = R.b :=
  sorry

/-- Completed divided-power differentials of the polynomial envelope `D`. -/
abbrev DividedPowerRetract.omegaPoly
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineOmegaD
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p

/-- Unfolding of the polynomial completed differentials of a retract. -/
theorem DividedPowerRetract.omegaPoly_eq
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaPoly =
      crystallineOmegaD
        (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p :=
  sorry

/-- Completed divided-power differentials of the smooth envelope `D'`. -/
abbrev DividedPowerRetract.omegaSmooth
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') : Type u :=
  crystallineOmegaD
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p

/-- Unfolding of the smooth completed differentials of a retract. -/
theorem DividedPowerRetract.omegaSmooth_eq
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaSmooth =
      crystallineOmegaD
        (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p :=
  sorry

/-- Uncompleted divided-power differential map induced by an `A`-algebra map of
completed envelopes, via `KaehlerDifferential.map`. -/
noncomputable def uncompletedFormsOfHom
    {D D' : Type u} [CommRing D] [CommRing D']
    (fD : A →+* D) (fD' : A →+* D')
    {JD : Ideal D} {JD' : Ideal D'}
    (γD : DividedPowers JD) (γD' : DividedPowers JD')
    (φ : D →+* D') (hA : φ.comp fD = fD')
    (hDP : γD.IsDPMorphism γD' φ) :
    letI : Algebra A D := fD.toAlgebra
    letI : Algebra A D' := fD'.toAlgebra
    -- Local instance justification (noncanonical choice): Algebra along φ vs a competing reverse map.
    letI : Algebra D D' := φ.toAlgebra
    letI : Module D (dividedPowerDifferential fD' γD') := Module.compHom _ φ
    dividedPowerDifferential fD γD →ₗ[D] dividedPowerDifferential fD' γD' :=
  letI : Algebra A D := fD.toAlgebra
  letI : Algebra A D' := fD'.toAlgebra
  -- Local instance justification (noncanonical choice): Algebra along φ vs a competing reverse map.
  letI : Algebra D D' := φ.toAlgebra
  letI : Module D (dividedPowerDifferential fD' γD') := Module.compHom _ φ
  -- Local instance justification (defeq pin): φ is used as an `A`-algebra map of envelopes.
  letI : IsScalarTower A D D' := IsScalarTower.of_algebraMap_eq' hA.symm
  { toFun := fun q =>
      (dividedPowerRelations fD' γD').mkQ
        (KaehlerDifferential.map A A D D' (Quotient.out q))
    map_add' := sorry
    map_smul' := sorry }

/-- Completed DP-differential map induced by an `A`-algebra map, obtained by
applying `uncompletedFormsOfHom` stagewise and completing. -/
noncomputable def formsOfHom
    {D D' : Type u} [CommRing D] [CommRing D']
    (fD : A →+* D) (fD' : A →+* D')
    {JD : Ideal D} {JD' : Ideal D'}
    (γD : DividedPowers JD) (γD' : DividedPowers JD')
    (φ : D →+* D') (hA : φ.comp fD = fD')
    (hDP : γD.IsDPMorphism γD' φ) :
    crystallineOmegaD fD γD p →+ crystallineOmegaD fD' γD' p :=
  letI : Algebra A D := fD.toAlgebra
  letI : Algebra A D' := fD'.toAlgebra
  -- Local instance justification (noncanonical choice): Algebra along φ vs a competing reverse map.
  letI : Algebra D D' := φ.toAlgebra
  letI : Module D (dividedPowerDifferential fD' γD') := Module.compHom _ φ
  AddMonoidHom.mk'
    (fun ω =>
      ⟨fun k =>
        (AdicCompletion.of (Ideal.span {(p : D')}) (dividedPowerDifferential fD' γD')
          (uncompletedFormsOfHom fD fD' γD γD' φ hA hDP
            (Quotient.out (ω.val k)))).val k
      , sorry⟩)
    sorry

/-- The Remark 60.6.9 comparison `φ : Ω_D → Ω_{D'}` induced by `a`. -/
noncomputable def DividedPowerRetract.formsA
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaPoly →+ R.omegaSmooth :=
  formsOfHom p
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    R.γbar R.γbar' R.a R.a_base R.a_isDP

/-- The Remark 60.6.9 comparison `Ω_{D'} → Ω_D` induced by `b`. -/
noncomputable def DividedPowerRetract.formsB
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.omegaSmooth →+ R.omegaPoly :=
  formsOfHom p
    (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    R.γbar' R.γbar R.b R.b_base R.b_isDP

/-- `formsA` is linear over `a`. -/
theorem DividedPowerRetract.formsA_smul
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.polyD) (ω : R.omegaPoly) :
    (R.formsA) (r • ω) = R.a r • (R.formsA) ω :=
  sorry

/-- `formsA` intertwines the universal derivations with `a`. -/
theorem DividedPowerRetract.formsA_der
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.polyD) :
    (R.formsA)
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p r) =
      crystallineOmegaD_derivation
        (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p (R.a r) :=
  sorry

/-- `formsB` is linear over `b`. -/
theorem DividedPowerRetract.formsB_smul
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.smoothD) (ω : R.omegaSmooth) :
    (R.formsB) (r • ω) = R.b r • (R.formsB) ω :=
  sorry

/-- `formsB` intertwines the universal derivations with `b`. -/
theorem DividedPowerRetract.formsB_der
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
    (r : R.smoothD) :
    (R.formsB)
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p r) =
      crystallineOmegaD_derivation
        (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p (R.b r) :=
  sorry

/-- Because `a ∘ b = id_{D'}`, the induced form maps satisfy `formsA ∘ formsB = id`. -/
theorem DividedPowerRetract.formsA_comp_formsB
    [Algebra.Smooth A P']
    (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') :
    R.formsA.comp R.formsB = AddMonoidHom.id _ :=
  sorry

end CrystallineConnectionPair

end
