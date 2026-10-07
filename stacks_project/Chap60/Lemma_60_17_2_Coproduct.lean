module

public import stacks_project.Chap60.Lemma_60_17_2_Object
public import stacks_project.Chap60.Lemma_60_17_1_Coprojection
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DividedPowers DividedPowers.PAdic CompletedCris

/-- The slot map `P → D(n)` preserves divided powers after composing with the envelope of the
tensor-power presentation. -/
theorem crystallineSlot_toEnvelope_isDPMorphism
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I) {ι : Type u} {n : ℕ}
    {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    DividedPowers.IsDPMorphism γ En.D.dividedPowers
      ((En.toD.comp (tensorPowerSlot A ι n j).toRingHom).comp
        (algebraMap A (MvPolynomial ι A))) := sorry

/-- The slot map sends the kernel of the polynomial presentation into the envelope ideal of `D(n)`. -/
theorem crystallineSlot_toEnvelope_ideal
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) {n : ℕ}
    {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom) (j : Fin (n + 1)) :
    Ideal.map (En.toD.comp (tensorPowerSlot A ι n j).toRingHom) J ≤ En.D.ideal := sorry

/-- The unique envelope lift of a tensor-power slot `P → D(n)`. -/
noncomputable def crystallineEnvelopeSlotLift
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    E.D ⟶ En.D :=
  Classical.choose
    (hE (En.toD.comp (tensorPowerSlot A ι n j).toRingHom)
      (crystallineSlot_toEnvelope_isDPMorphism γ En j)
      (crystallineSlot_toEnvelope_ideal γ π En hJ j))

/-- The envelope lift recovers the tensor-power slot on the polynomial presentation. -/
theorem crystallineEnvelopeSlotLift_spec
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    (crystallineEnvelopeSlotLift γ π hJ E hE En j).toRingHom.comp E.toD =
      En.toD.comp (tensorPowerSlot A ι n j).toRingHom := sorry

/-- Powers of `(p)` pull back along the envelope slot lift. -/
theorem crystallineEnvelopeSlotLift_span_pow
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (p : ℕ) {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) (k : ℕ) :
    Ideal.span {(p : E.D)} ^ k ≤
      (Ideal.span {(p : En.D)} ^ k).comap
        (crystallineEnvelopeSlotLift γ π hJ E hE En j).toRingHom := sorry

/-- Stage maps of the completed slot lift, as maps into the tensor-power envelope quotients. -/
noncomputable def crystallineDCrisCoprojStage
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (p : ℕ)
    {I : Ideal A} (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) (k : ℕ) :
    AdicCompletion (Ideal.span {(p : E.D)}) E.D →+*
      En.D ⧸ Ideal.span {(p : En.D)} ^ k :=
  (Ideal.quotientMap (Ideal.span {(p : En.D)} ^ k)
      (crystallineEnvelopeSlotLift γ π hJ E hE En j).toRingHom
      (crystallineEnvelopeSlotLift_span_pow p γ π hJ E hE En j k)).comp
    (AdicCompletion.evalₐ (Ideal.span {(p : E.D)}) k).toRingHom

/-- Compatibility of the completed slot stages with the canonical factor maps. -/
theorem crystallineDCrisCoprojStage_compat
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (p : ℕ)
    {I : Ideal A} (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) {m k : ℕ} (hle : m ≤ k) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : En.D)}) hle).comp
        (crystallineDCrisCoprojStage p γ π hJ E hE En j k) =
      crystallineDCrisCoprojStage p γ π hJ E hE En j m := sorry

/-- The underlying ring map of the completed crystalline coprojection `D → D(n)`. -/
noncomputable def crystallineDCrisCoprojRingHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (p : ℕ)
    {I : Ideal A} (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (tensorPowerCarrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    AdicCompletion (Ideal.span {(p : E.D)}) E.D →+*
      AdicCompletion (Ideal.span {(p : En.D)}) En.D :=
  AdicCompletion.liftRingHom (Ideal.span {(p : En.D)})
    (fun k ↦ crystallineDCrisCoprojStage p γ π hJ E hE En j k)
    (fun {_ _} hle ↦ crystallineDCrisCoprojStage_compat p γ π hJ E hE En j hle)

/-- The completed slot lift is a divided-power morphism of the envelope completions. -/
theorem crystallineDCrisCoprojRingHom_isDPMorphism
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    IsDPMorphism
      (crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E ND hND γD hγD).B.dividedPowers
      (crystallineDnCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En Nn hNn γn hγn).B.dividedPowers
      (crystallineDCrisCoprojRingHom p γ π hJ E hE En j) := sorry

/-- The coprojections `D → D(n)` in `Cris^∧(C/A)`, indexed by the `n + 1` tensor factors. -/
noncomputable def crystallineDCrisCoproj
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E ND hND γD hγD ⟶
      crystallineDnCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En Nn hNn γn hγn :=
  Hom.of γ (algebraMap A C) hIC hpnil
    (DPMorphism.mk'
      (crystallineDCrisCoprojRingHom_isDPMorphism p I γ π hπ J hJ hIC hpnil hIJ E hE
        ND hND γD hγD Jn hJn hIJn En Nn hNn γn hγn j))
    sorry sorry

/-- The completed coprojection is compatible with the tensor-power slot on `P`. -/
theorem crystallineDCrisCoproj_slot
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) (x : MvPolynomial ι A) :
    (crystallineDCrisCoproj p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
          Jn hJn hIJn En Nn hNn γn hγn j).map.toRingHom
        (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D) (E.toD x)) =
      algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)
        (En.toD (tensorPowerSlot A ι n j x)) := sorry

/-- The cofan of `n + 1` copies of `D` with vertex `D(n)` in `Cris^∧(C/A)`. -/
noncomputable def crystallineDnCofan
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D))) :
    Cofan (fun _ : Fin (n + 1) ↦
      crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E ND hND γD hγD) :=
  Cofan.mk
    (crystallineDnCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En Nn hNn γn hγn)
    (fun j ↦
      crystallineDCrisCoproj p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
        Jn hJn hIJn En Nn hNn γn hγn j)

/-- A family of maps `D → T` induces a map `D(n) → T` in `Cris^∧(C/A)`. -/
theorem crystallineDn_exists_desc
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (T : DividedPowerThickening.CrisWedgeObject p A I γ C (algebraMap A C) hIC hpnil)
    (s : Fin (n + 1) →
      (crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E ND hND γD hγD ⟶ T)) :
    ∃ d : crystallineDnCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En Nn hNn γn hγn ⟶ T,
      ∀ j : Fin (n + 1),
        crystallineDCrisCoproj p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
              Jn hJn hIJn En Nn hNn γn hγn j ≫ d = s j := sorry

/-- A morphism `D(n) → T` is uniquely determined by its composites with the coprojections. -/
theorem crystallineDn_desc_unique
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (T : DividedPowerThickening.CrisWedgeObject p A I γ C (algebraMap A C) hIC hpnil)
    (d₁ d₂ : crystallineDnCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En Nn hNn γn hγn ⟶ T)
    (hd : ∀ j : Fin (n + 1),
      crystallineDCrisCoproj p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
            Jn hJn hIJn En Nn hNn γn hγn j ≫ d₁ =
        crystallineDCrisCoproj p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
            Jn hJn hIJn En Nn hNn γn hγn j ≫ d₂) :
    d₁ = d₂ := sorry
