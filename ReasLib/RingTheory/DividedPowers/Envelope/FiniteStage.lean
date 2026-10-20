module

public import ReasLib.RingTheory.DividedPowers.Envelope.Universal
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

namespace DividedPowers.PAdic

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (J : Ideal P)

/-- The finite quotient `P_e = P / p^e P`. -/
abbrev quotient (e : ℕ) : Type u := P ⧸ Ideal.span {((p : P) ^ e)}

/-- The image `J_e` of `J` in the finite quotient `P_e`. -/
def stageIdeal (e : ℕ) : Ideal (quotient p P e) :=
  Ideal.map (Ideal.Quotient.mk (Ideal.span {((p : P) ^ e)})) J

/-- The structure map `A →+* P_e` induced by the quotient map. -/
def stageMap (e : ℕ) : A →+* quotient p P e :=
  (Ideal.Quotient.mk (Ideal.span {((p : P) ^ e)})).comp (algebraMap A P)

/-- The base divided-power ideal maps into the induced finite-stage ideal. -/
theorem stageIdeal_contains_base
    (hIJ : Ideal.map (algebraMap A P) I ≤ J) (e : ℕ) :
    Ideal.map (stageMap p A P e) I ≤ stageIdeal p P J e := sorry

/-- The divided-power envelope of the finite presentation `(P_e, J_e)`. -/
abbrev envelopeStage (hIJ : Ideal.map (algebraMap A P) I ≤ J) (e : ℕ) :=
  DividedPowerEnvelope I γ (stageMap p A P e)
    (stageIdeal p P J e) (stageIdeal_contains_base p A P I J hIJ e)

/-- The base-map formula for a finite-stage envelope. -/
theorem envelopeStage_base
    (hIJ : Ideal.map (algebraMap A P) I ≤ J) (e : ℕ)
    (Eₑ : envelopeStage p A P I γ J hIJ e) :
    Eₑ.base.toRingHom = Eₑ.toD.comp (stageMap p A P e) := sorry

/-- The base divided-power ideal is contained in the kernel presentation ideal. -/
theorem pAdicBaseIdealLeKernel
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    (I : Ideal A) (f : A →+* C) (π : P →+* C) [Algebra A P]
    (J : Ideal P)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (hJ : J = RingHom.ker π) :
    Ideal.map (algebraMap A P) I ≤ J := sorry

/-- The presentation map from `P` to a finite divided-power envelope stage. -/
def envelopeStageFromP
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    P →+* EStage.D :=
  EStage.toD.comp (Ideal.Quotient.mk (Ideal.span {((p : P) ^ e)}))

/-- The image of `J` under `envelopeStageFromP` lies in the distinguished ideal of the finite envelope stage. -/
theorem envelopeStageFromP_ideal_le
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    J ≤ Ideal.comap (envelopeStageFromP p e EStage) EStage.D.ideal := sorry

/-- The quotient map from `C` to the finite envelope quotient induced by the presentation. -/
noncomputable def envelopeStageQuotientMap
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    C →+* (EStage.D ⧸ EStage.D.ideal) :=
  (Ideal.quotientMap EStage.D.ideal (envelopeStageFromP p e EStage)
      (envelopeStageFromP_ideal_le p e EStage)).comp
    ((Ideal.quotEquivOfEq hJ.symm).toRingHom.comp
      (π.quotientKerEquivOfSurjective hπ).symm.toRingHom)

/-- The quotient square for a finite envelope stage commutes. -/
theorem envelopeStageQuotientMap_comm
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    (Ideal.Quotient.mk EStage.D.ideal).comp EStage.base.toRingHom =
      (envelopeStageQuotientMap p π hπ hJ e EStage).comp f := sorry

/-- The prime `p` is nilpotent in every finite envelope stage. -/
theorem envelopeStage_p_nilpotent
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    IsNilpotent (p : EStage.D) := sorry

/-- The presentation map to `C` preserves the divided powers on the base ideal. -/
theorem envelopePresentationToC_isDPMorphism
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I} [Algebra A P]
    (π : P →+* C) {J : Ideal P} (hJ : J = RingHom.ker π)
    (hIJ : Ideal.map (algebraMap A P) I ≤ J) :
    DividedPowers.IsDPMorphism γ (dividedPowersBot C)
      (π.comp (algebraMap A P)) := sorry

/-- The kernel presentation ideal maps to the zero ideal in `C`. -/
theorem envelopePresentationToC_ideal
    {P C : Type u} [CommRing P] [CommRing C]
    (π : P →+* C) {J : Ideal P} (hJ : J = RingHom.ker π) :
    Ideal.map π J ≤ (⊥ : Ideal C) := sorry

/-- The canonical divided-power quotient `D → C`, obtained from universality. -/
noncomputable def envelopeToC
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I} [Algebra A P]
    (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E) :
    E.D →+* C :=
  (Classical.choose (ExistsUnique.exists
    (@hE (DividedPowerRing.of C ⊥ (dividedPowersBot C)) π
      (envelopePresentationToC_isDPMorphism π hJ hIJ)
      (envelopePresentationToC_ideal π hJ)))).toRingHom

/-- The canonical envelope quotient extends the presentation of `C`. -/
theorem envelopeToC_comp
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I} [Algebra A P]
    (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E) :
    (envelopeToC π hπ hJ E hE).comp E.toD = π := sorry

/-- The envelope quotient map annihilates the distinguished ideal. -/
theorem envelopeToC_ideal
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I} [Algebra A P]
    (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E) :
    E.D.ideal ≤ RingHom.ker (envelopeToC π hπ hJ E hE) := sorry

end DividedPowers.PAdic
