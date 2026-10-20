/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.RingTheory.AdicCompletion.Polynomial

/-!
# Evaluation of adically completed polynomial rings

Evaluation at a tuple in an adically complete algebra is constructed from
compatible evaluations modulo powers of the coefficient ideal.
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A ι : Type u} [CommRing A]

/-- The image of the indeterminate `MvPolynomial.X i` in `A[x_ι]^∧`. -/
def X (I : Ideal A) (i : ι) : polynomialCompletion A I ι :=
  AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) (MvPolynomial.X i)

variable {C : Type u} [CommRing C] [Algebra A C]

/-- Finite-stage evaluation of an element of `A[x_ι]^∧` at a tuple `v`, landing in
`C ⧸ (I.map (algebraMap A C)) ^ n`. -/
def adicAevalStage (I : Ideal A) (v : ι → C) (n : ℕ) :
    polynomialCompletion A I ι →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n :=
  (Ideal.quotientEquivAlgOfEq A (Ideal.map_pow (algebraMap A C) I n)).toAlgHom.comp
    (((MvPolynomial.aeval fun i ↦
        Ideal.Quotient.mk ((I ^ n).map (algebraMap A C)) (v i)).restrictScalars A).comp
      (IAdicRestrictedPowerSeries.stageHom ι I n))

/-- Finite-stage evaluation sends the indeterminate `X I i` to the residue of `v i`. -/
theorem adicAevalStage_X (I : Ideal A) (v : ι → C) (n : ℕ) (i : ι) :
    adicAevalStage I v n (X I i) =
      Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (v i) :=
  sorry

/-- Finite-stage evaluations are compatible with the inverse system of quotients
`C ⧸ (I C) ^ n`. -/
theorem adicAevalStage_compatible (I : Ideal A) (v : ι → C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (adicAevalStage I v n) =
      adicAevalStage I v m :=
  sorry

/-- The `A`-algebra map `A[x_ι]^∧ →ₐ[A] C` evaluating the variables at `v`,
obtained from the inverse-limit universal property of an `I`-adically complete algebra.
Uniqueness among all such maps holds under finite generation of `I`; see `eq_adicAeval`. -/
def adicAeval (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C) :
    polynomialCompletion A I ι →ₐ[A] C :=
  IsAdicComplete.liftAlgHom (I.map (algebraMap A C)) (fun n ↦ adicAevalStage I v n)
    (adicAevalStage_compatible I v)

/-- Completed evaluation sends the indeterminate `X I i` to `v i`. -/
theorem adicAeval_X (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C)
    (i : ι) : adicAeval I v (X I i) = v i :=
  sorry

/-- Completed evaluation extends ordinary polynomial evaluation along the dense map
from `A[x_ι]`. -/
theorem adicAeval_comp_of (I : Ideal A) [IsAdicComplete (I.map (algebraMap A C)) C] (v : ι → C)
    (p : MvPolynomial ι A) :
    adicAeval I v (AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p) =
      MvPolynomial.aeval v p :=
  sorry

/-- An `A`-algebra map out of `A[x_ι]^∧` into an `I`-adically complete algebra is
evaluation at the images of the indeterminates, provided `I` is finitely generated
(so the inverse-limit kernels agree with the powers `I^n • polynomialCompletion`). -/
theorem eq_adicAeval {I : Ideal A} (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) :
    ψ = adicAeval I fun i ↦ ψ (X I i) :=
  sorry

/-- The perturbation of `ψ` sending `X I i` to `ψ (X I i) + δ i`. -/
def aevalShift {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) :
    polynomialCompletion A I ι →ₐ[A] C :=
  adicAeval I fun i ↦ ψ (X I i) + δ i

/-- The shifted map sends the indeterminate `X I i` to `ψ (X I i) + δ i`. -/
theorem aevalShift_X {I : Ideal A} [IsAdicComplete (I.map (algebraMap A C)) C]
    (ψ : polynomialCompletion A I ι →ₐ[A] C) (δ : ι → C) (i : ι) :
    aevalShift ψ δ (X I i) = ψ (X I i) + δ i :=
  sorry

end Algebra.NaiveCotangent.Adic
