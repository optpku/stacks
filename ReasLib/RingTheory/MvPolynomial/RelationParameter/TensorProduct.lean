/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.MvPolynomial.RelationParameter

/-!
# Tensor products of polynomial relation parameters

This module gives the evaluation map for a polynomial relation-parameter
algebra and records its exactness and coefficient-specialization properties.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial.RelationParameter

/-- Evaluation of polynomials over the relation-parameter algebra in the tensor product of
the presented algebra with that coefficient algebra. -/
noncomputable def evaluationMap
    {C : Type u} {B : Type v} [CommRing C] [CommRing B] [Algebra C B]
    {n m K : ℕ} (x : Fin n → B) (f : Fin m → MvPolynomial (Fin n) C)
    (Ω : Finset (Fin n →₀ ℕ)) :
    MvPolynomial (Fin n) (CoefficientAlgebra C K f Ω) →+*
      B ⊗[C] CoefficientAlgebra C K f Ω :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight :
      CoefficientAlgebra C K f Ω →ₐ[C] B ⊗[C] CoefficientAlgebra C K f Ω).toRingHom
    (fun i ↦ (Algebra.TensorProduct.includeLeft :
      B →ₐ[C] B ⊗[C] CoefficientAlgebra C K f Ω) (x i))

/-- Exactness and terminal surjectivity of the coefficient-extended polynomial presentation. -/
theorem exact_equationMap_evaluationMap
    {C : Type u} {B : Type v} [CommRing C] [CommRing B] [Algebra C B]
    {n m K : ℕ} (x : Fin n → B) (f : Fin m → MvPolynomial (Fin n) C)
    (Ω : Finset (Fin n →₀ ℕ)) (h_f_support : ∀ j, (f j).support ⊆ Ω)
    (h_exact : Function.Exact
      (Finsupp.linearCombination (MvPolynomial (Fin n) C) f)
      (MvPolynomial.aeval x : MvPolynomial (Fin n) C →ₐ[C] B))
    (h_surjective : Function.Surjective
      (MvPolynomial.aeval x : MvPolynomial (Fin n) C →ₐ[C] B)) :
    Function.Exact (equationMap C (K := K) f Ω) (evaluationMap (K := K) x f Ω) ∧
      Function.Surjective (evaluationMap (K := K) x f Ω) := sorry

/-- Specializing the universal coefficients to the coefficients of a supported relation family
identifies that family, the coefficient-extended equations, and the tensor-product evaluation
map. -/
theorem maps_baseChange
    {C : Type u} {B : Type v} {Rhat : Type w}
    [CommRing C] [CommRing B] [CommRing Rhat] [Algebra C B] [Algebra C Rhat]
    {n m K : ℕ} (x : Fin n → B) (f : Fin m → MvPolynomial (Fin n) C)
    (Ω : Finset (Fin n →₀ ℕ)) (a : Fin K → Fin m →₀ MvPolynomial (Fin n) Rhat)
    (h_f_support : ∀ j, (f j).support ⊆ Ω)
    (h_a_support : ∀ k j, (a k j).support ⊆ Ω)
    (tildeσ : CoefficientAlgebra C K f Ω →ₐ[C] Rhat)
    (h_tildeσ : ∀ k j (I : Ω),
      tildeσ ((algebraMap (MvPolynomial (Fin K × Fin m × Ω) C)
        (CoefficientAlgebra C K f Ω)) (MvPolynomial.X (k, j, I))) =
        MvPolynomial.coeff I.1 (a k j)) :
    let mapCoefficients := MvPolynomial.map tildeσ.toRingHom
    ((fun k ↦ Finsupp.mapRange mapCoefficients mapCoefficients.map_zero
        (vector C f Ω k)),
      (fun j ↦ mapCoefficients
        (MvPolynomial.map (algebraMap C (CoefficientAlgebra C K f Ω)) (f j))),
      (Algebra.TensorProduct.map (AlgHom.id C B) tildeσ).toRingHom.comp
        (evaluationMap (K := K) x f Ω)) =
      (a, (fun j ↦ MvPolynomial.map (algebraMap C Rhat) (f j)),
        (MvPolynomial.eval₂Hom
          (Algebra.TensorProduct.includeRight : Rhat →ₐ[C] B ⊗[C] Rhat).toRingHom
          (fun i ↦ (Algebra.TensorProduct.includeLeft : B →ₐ[C] B ⊗[C] Rhat) (x i))).comp
            mapCoefficients) := sorry

end MvPolynomial.RelationParameter
