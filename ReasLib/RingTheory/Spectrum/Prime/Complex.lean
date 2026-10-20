/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime spectra of the complex numbers and their real tensor square

The map `Spec(ℂ) → Spec(ℝ)` is bijective on points, but its base change along itself is not
injective. The latter fact is witnessed by the kernels of multiplication and conjugate
multiplication on `ℂ ⊗[ℝ] ℂ`.
-/

@[expose] public section

open scoped TensorProduct

/-- The map on prime spectra induced by `ℝ → ℂ` is bijective. -/
theorem complexSpecToRealSpec_bijective :
    Function.Bijective (PrimeSpectrum.comap (algebraMap ℝ ℂ)) := by
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  · intro y
    let x : PrimeSpectrum ℂ := Classical.choice inferInstance
    exact ⟨x, Subsingleton.elim _ _⟩

/-- The map on prime spectra induced by the left inclusion into `ℂ ⊗[ℝ] ℂ` is not injective. -/
@[stacks 0496]
theorem complexTensorSquareSpecToComplexSpec_not_injective :
    ¬ Function.Injective (PrimeSpectrum.comap (algebraMap ℂ (ℂ ⊗[ℝ] ℂ))) := by
  let mul : ℂ ⊗[ℝ] ℂ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (AlgHom.id ℝ ℂ)
      (fun _ _ => Commute.all _ _)
  let conjMul : ℂ ⊗[ℝ] ℂ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) Complex.conjAe.toAlgHom
      (fun _ _ => Commute.all _ _)
  let p : PrimeSpectrum (ℂ ⊗[ℝ] ℂ) :=
    ⟨RingHom.ker mul.toRingHom, RingHom.ker_isPrime _⟩
  let q : PrimeSpectrum (ℂ ⊗[ℝ] ℂ) :=
    ⟨RingHom.ker conjMul.toRingHom, RingHom.ker_isPrime _⟩
  have hpq : p ≠ q := by
    intro h
    have hm : Complex.I ⊗ₜ[ℝ] (1 : ℂ) - (1 : ℂ) ⊗ₜ[ℝ] Complex.I ∈ p.asIdeal := by
      change mul (Complex.I ⊗ₜ[ℝ] (1 : ℂ) - (1 : ℂ) ⊗ₜ[ℝ] Complex.I) = 0
      simp [mul]
    have hc : Complex.I ⊗ₜ[ℝ] (1 : ℂ) - (1 : ℂ) ⊗ₜ[ℝ] Complex.I ∉ q.asIdeal := by
      change conjMul (Complex.I ⊗ₜ[ℝ] (1 : ℂ) - (1 : ℂ) ⊗ₜ[ℝ] Complex.I) ≠ 0
      simp [conjMul, Complex.I_ne_zero]
    exact hc (h ▸ hm)
  intro h
  apply hpq
  apply h
  apply PrimeSpectrum.ext
  ext z
  simp [p, q, mul, conjMul]
