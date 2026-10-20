/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.TensorPower
public import ReasLib.RingTheory.AdicCompletion.Nat
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DividedPowers DividedPowers.PAdic CompletedCris

namespace DividedPowerEnvelope.TensorPower

/-- The completed envelope of a diagonal tensor presentation is a completed crystalline object. -/
noncomputable def completedCrisObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJ : J = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil :=
  envelopeCompletedCrisObject p γ (algebraMap A C) (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom
    (MvPolynomial.TensorPower.diagonal_surjective A ι π hπ n) (MvPolynomial.TensorPower.diagonal A ι π n).comp_algebraMap
    hIC hpnil hJ E hE N hN γhat hγhat

/-- The underlying divided-power ring is the completion of the tensor envelope. -/
theorem completedCrisObject_B
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJ : J = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (completedCrisObject p I γ π hπ n hIC hpnil J hJ hIJ E hE N hN γhat hγhat).B =
      envelopeCompletionRing p A (MvPolynomial.TensorPower.carrier A ι n) I γ J hIJ E N hN γhat := by
  exact envelopeCompletedCrisObject_B p γ (algebraMap A C)
    (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom
    (MvPolynomial.TensorPower.diagonal_surjective A ι π hπ n)
    (MvPolynomial.TensorPower.diagonal A ι π n).comp_algebraMap
    hIC hpnil hJ E hE N hN γhat hγhat

/-- The slot map `P → D(n)` preserves divided powers after composing with the envelope of the
tensor-power presentation. -/
private theorem slot_toEnvelope_isDPMorphism
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I) {ι : Type u} {n : ℕ}
    {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
    {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    DividedPowers.IsDPMorphism γ En.D.dividedPowers
      ((En.toD.comp (MvPolynomial.TensorPower.slot A ι n j).toRingHom).comp
        (algebraMap A (MvPolynomial ι A))) := sorry

/-- The slot map sends the kernel of the polynomial presentation into the envelope ideal of `D(n)`. -/
private theorem slot_toEnvelope_ideal
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) {n : ℕ}
    {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom) (j : Fin (n + 1)) :
    Ideal.map (En.toD.comp (MvPolynomial.TensorPower.slot A ι n j).toRingHom) J ≤ En.D.ideal := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro polynomial hpolynomial
  have hpolynomial_kernel : π polynomial = 0 := by
    simpa [hJ] using hpolynomial
  have hslot : MvPolynomial.TensorPower.slot A ι n j polynomial ∈ Jn := by
    rw [hJn, RingHom.mem_ker]
    exact (MvPolynomial.TensorPower.diagonal_slot A ι π n j polynomial).trans hpolynomial_kernel
  exact En.ideal_map (Ideal.mem_map_of_mem En.toD hslot)

/-- The unique envelope lift of a tensor-power slot `P → D(n)`. -/
private noncomputable def slotLift
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    E.D ⟶ En.D :=
  Classical.choose
    (hE (En.toD.comp (MvPolynomial.TensorPower.slot A ι n j).toRingHom)
      (slot_toEnvelope_isDPMorphism γ En j)
      (slot_toEnvelope_ideal γ π hJn En hJ j))

/-- The envelope lift recovers the tensor-power slot on the polynomial presentation. -/
private theorem slotLift_spec
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {I : Ideal A}
    (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    (slotLift γ π hJ E hE hJn En j).toRingHom.comp E.toD =
      En.toD.comp (MvPolynomial.TensorPower.slot A ι n j).toRingHom := sorry

/-- The scalar-adic completion of a universal envelope slot lift. -/
private noncomputable def completedSlotRingHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (p : ℕ)
    {I : Ideal A} (γ : DividedPowers I) {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
    {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    {n : ℕ} {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (j : Fin (n + 1)) :
    AdicCompletion (Ideal.span {(p : E.D)}) E.D →+*
      AdicCompletion (Ideal.span {(p : En.D)}) En.D :=
  AdicCompletion.Nat.map p (slotLift γ π hJ E hE hJn En j).toRingHom

/-- The completed slot lift is a divided-power morphism of the envelope completions. -/
private theorem coprojection_isDPMorphism
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    IsDPMorphism
      (envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD).B.dividedPowers
      (completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn).B.dividedPowers
      (completedSlotRingHom p γ π hJ E hE hJn En j) := sorry

/-- The completed slot lift commutes with the base divided-power maps. -/
private theorem coprojection_base_comm
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    (DPMorphism.mk'
      (coprojection_isDPMorphism p I γ π hπ J hJ hIC hpnil hIJ E hE
        ND hND γD hγD Jn hJn hIJn En hEn Nn hNn γn hγn j)).toRingHom.comp (envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD).base.toRingHom =
      (completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn).base.toRingHom := sorry

/-- The completed slot lift commutes with the maps to the target ring. -/
private theorem coprojection_quotient_comm
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    (completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn).toC.comp (DPMorphism.mk'
      (coprojection_isDPMorphism p I γ π hπ J hJ hIC hpnil hIJ E hE
        ND hND γD hγD Jn hJn hIJn En hEn Nn hNn γn hγn j)).toRingHom =
      (envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD).toC := sorry

/-- The coprojections `D → D(n)` in `Cris^∧(C/A)`, indexed by the `n + 1` tensor factors. -/
@[no_expose]
noncomputable def coprojection
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) :
    envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD ⟶
      completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn :=
  Hom.of γ (algebraMap A C) hIC hpnil
    (DPMorphism.mk'
      (coprojection_isDPMorphism p I γ π hπ J hJ hIC hpnil hIJ E hE
        ND hND γD hγD Jn hJn hIJn En hEn Nn hNn γn hγn j))
    (coprojection_base_comm p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
      Jn hJn hIJn En hEn Nn hNn γn hγn j)
    (coprojection_quotient_comm p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
      Jn hJn hIJn En hEn Nn hNn γn hγn j)

/-- The completed coprojection is compatible with the tensor-power slot on `P`. -/
theorem coprojection_slot
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (j : Fin (n + 1)) (polynomial : MvPolynomial ι A) :
    (coprojection p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
          Jn hJn hIJn En hEn Nn hNn γn hγn j).map.toRingHom
        (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D) (E.toD polynomial)) =
      algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)
        (En.toD (MvPolynomial.TensorPower.slot A ι n j polynomial)) := sorry

/-- The cofan of `n + 1` copies of `D` with vertex `D(n)` in `Cris^∧(C/A)`. -/
noncomputable def cofan
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D))) :
    Cofan (fun _ : Fin (n + 1) ↦
      envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD) :=
  Cofan.mk
    (completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn)
    (fun j ↦
      coprojection p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
        Jn hJn hIJn En hEn Nn hNn γn hγn j)

/-- A family of maps `D → T` induces a map `D(n) → T` in `Cris^∧(C/A)`. -/
theorem exists_desc
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (T : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)
    (maps : Fin (n + 1) →
      (envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD ⟶ T)) :
    ∃ descent : completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn ⟶ T,
      ∀ j : Fin (n + 1),
        coprojection p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
              Jn hJn hIJn En hEn Nn hNn γn hγn j ≫ descent = maps j := sorry

/-- A morphism `D(n) → T` is uniquely determined by its composites with the coprojections. -/
theorem desc_unique
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))
    (T : CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)
    (first second : completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn ⟶ T)
    (hd : ∀ j : Fin (n + 1),
      coprojection p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
            Jn hJn hIJn En hEn Nn hNn γn hγn j ≫ first =
        coprojection p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
            Jn hJn hIJn En hEn Nn hNn γn hγn j ≫ second) :
    first = second := sorry

/-- The completed tensor envelope is the coproduct of its completed polynomial factors. -/
theorem isCoproduct
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
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D))) :
    Nonempty
      (IsColimit
        (cofan p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
          Jn hJn hIJn En hEn Nn hNn γn hγn)) := sorry

end DividedPowerEnvelope.TensorPower
