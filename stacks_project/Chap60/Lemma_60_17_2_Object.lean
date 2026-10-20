/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import stacks_project.Chap60.«60_17_0_4_TensorPower»

@[expose] public section

universe u

open DividedPowers DividedPowers.PAdic

/-- The iterated tensor-power presentation remains surjective onto `C`. -/
private theorem tensorPowerAlgHom_surjective
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {ι : Type u}
    (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ) :
    Function.Surjective (tensorPowerAlgHom π n) := by
  intro value
  obtain ⟨polynomial, hpolynomial⟩ := hπ value
  cases n with
  | zero => exact ⟨polynomial, hpolynomial⟩
  | succ stage =>
      refine ⟨polynomial ⊗ₜ[A] 1, ?_⟩
      change Algebra.TensorProduct.productMap π (tensorPowerAlgHom π stage)
        (polynomial ⊗ₜ[A] 1) = value
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, hpolynomial]

/-- The completed envelope of the `(n + 1)`-fold tensor-power presentation as a
`Cris^∧(C/A)` object. -/
noncomputable def crystallineDnCrisObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (tensorPowerCarrier A ι n)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil :=
  envelopeCompletedCrisObject p γ (algebraMap A C) (tensorPowerAlgHom π n).toRingHom
    (by exact tensorPowerAlgHom_surjective π hπ n) (tensorPowerAlgHom π n).comp_algebraMap
    hIC hpnil hJ E hE N hN γhat hγhat
