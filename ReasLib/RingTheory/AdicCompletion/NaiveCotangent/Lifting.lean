/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Obstruction
public import ReasLib.RingTheory.AdicCompletion.Polynomial.LinearApproximation
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType

/-!
# Correcting and descending lifts of adic algebra maps
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B C ι : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Subtracting representatives of a Jacobian homotopy from the variable images
sends every presentation relation into the square of the reduced ideal power. -/
theorem improve_mem_pow [Fintype ι] [DecidableEq ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] {P : Presentation A B I ι}
    {n n' : ℕ} (hn : n' ≤ n) {ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (h : (ι → B) →ₗ[B]
      coefficientModule I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn))
    (hcomm : map_obstructionHom hn hψ = h.comp (jacobian P))
    (hδh : ∀ i, Ideal.toCotangent (I.map (algebraMap A C) ^ n') ⟨δ i, hδ i⟩ =
      h (Pi.single i 1))
    {g : polynomialCompletion A I ι} (hg : g ∈ P.ker) :
    aevalShift ψ (fun i ↦ -δ i) g ∈ (I.map (algebraMap A C)) ^ (2 * n') :=
  sorry

/-- The corrected evaluation modulo the doubled reduced exponent kills the
presentation kernel when the corrections represent a Jacobian homotopy. -/
theorem improve_ker_le [Fintype ι] [DecidableEq ι] {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] {P : Presentation A B I ι}
    {n n' : ℕ} (hn : n' ≤ n) {ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (h : (ι → B) →ₗ[B]
      coefficientModule I ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn))
    (hcomm : map_obstructionHom hn hψ = h.comp (jacobian P))
    (hδh : ∀ i, Ideal.toCotangent (I.map (algebraMap A C) ^ n') ⟨δ i, hδ i⟩ =
      h (Pi.single i 1)) :
    RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (aevalShift ψ (fun i ↦ -δ i))).toRingHom :=
  sorry

/-- A corrected completed evaluation whose reduction kills the presentation
kernel descends to an algebra map from the presented algebra. -/
def improveAlgHom {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (P : Presentation A B I ι) {n' : ℕ} (ψ : polynomialCompletion A I ι →ₐ[A] C)
    (δ : ι → C)
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (aevalShift ψ (fun i ↦ -δ i))).toRingHom) :
    B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n') :=
  AlgHom.liftOfSurjective P.toAlgHom P.surjective
    ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
      (aevalShift ψ (fun i ↦ -δ i))) hker

/-- Composing the descended corrected map with its presentation gives the
corrected completed evaluation followed by reduction. -/
theorem improveAlgHom_comp {I : Ideal A}
    [IsAdicComplete (I.map (algebraMap A C)) C] (P : Presentation A B I ι) {n' : ℕ}
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C)
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (aevalShift ψ (fun i ↦ -δ i))).toRingHom) :
    (improveAlgHom P ψ δ hker).comp P.toAlgHom =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
        (aevalShift ψ (fun i ↦ -δ i)) :=
  sorry

/-- For a finitely generated coefficient ideal, corrections lying in the
reduced ideal power leave the descended map unchanged after reduction to that power. -/
theorem improveAlgHom_comp_factor {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] (P : Presentation A B I ι)
    {n n' : ℕ} (hn : n' ≤ n) (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ) (δ : ι → C)
    (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (hker : RingHom.ker P.toAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp
          (aevalShift ψ (fun i ↦ -δ i))).toRingHom) :
    (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n' zero_lt_two))).comp
        (improveAlgHom P ψ δ hker) =
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn)).comp ψn :=
  sorry

/-- Over a Noetherian base, vanishing of the coefficient-changed obstruction
for `n' < n < 2*n'` gives a map modulo `I^{2n'} C` agreeing with the original
residue map modulo `I^{n'} C`. -/
theorem exists_hom_of_map_obstructionClass_eq_zero [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n n' : ℕ} (hn : n' < n) (hhalf : n < 2 * n')
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : map_obstructionClass hn.le hψ = 0) :
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n' zero_lt_two))).comp ψ' =
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn.le)).comp ψn :=
  sorry

/-- Over a Noetherian base, vanishing of the obstruction of a residue map
modulo `I^n C` gives a lift modulo `I^{2n} C` with the original reduction. -/
theorem exists_hom_of_obstructionClass_eq_zero [IsNoetherianRing A]
    {I : Ideal A} [Algebra.TopologicallyFiniteType I B]
    [IsAdicComplete (I.map (algebraMap A C)) C] [Fintype ι]
    (P : Presentation A B I ι) {n : ℕ}
    (ψn : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (hψ : IsLift P ψn ψ)
    (hobs : obstructionClass hψ = 0) :
    ∃ ψ' : B →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n),
      (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n zero_lt_two))).comp ψ' =
        ψn :=
  sorry

end Algebra.NaiveCotangent.Adic
