/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjectivity under tensor-order exchange

Mathlib exposes extension of scalars both as `LinearMap.baseChange` and as a
right tensor map.  Their carriers differ by the canonical tensor commutation
equivalence, so surjectivity is the same.  This low-level bridge is independent
of spectra and support and can be reused by any fiber or base-change argument.
It is shared support for comparing localized and residue-fiber surjectivity
(`@stack 05GE`); the declaration itself is neutral infrastructure.

@stack 05GE
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Surjectivity is unchanged by switching between left base-change and right-tensor presentations
of extension of scalars. -/
theorem baseChange_surjective_iff_rTensor_surjective
    (φ : M →ₗ[R] N) (A : Type*) [Semiring A] [Algebra R A] :
    Function.Surjective (φ.baseChange A) ↔
      Function.Surjective (φ.rTensor A) := by
  change Function.Surjective (φ.lTensor A) ↔ Function.Surjective (φ.rTensor A)
  exact LinearMap.lTensor_surj_iff_rTensor_surj (M := A) (f := φ)

/-- For a surjective scalar map, the kernel of `m ↦ 1 ⊗ m` is the scalar
kernel times the whole module. -/
theorem ker_tensorProductMk_of_surjective
    {R K M : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup M] [Module R M]
    (hsurjective : Function.Surjective (algebraMap R K)) :
    LinearMap.ker (TensorProduct.mk R K M (1 : K)) =
      (RingHom.ker (algebraMap R K)) • (⊤ : Submodule R M) := by
  let I : Ideal R := RingHom.ker (algebraMap R K)
  let eAlg : (R ⧸ I) ≃ₐ[R] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R K) hsurjective
  let eLin : (R ⧸ I) ≃ₗ[R] K := eAlg.toLinearEquiv
  let eTensor : TensorProduct R (R ⧸ I) M ≃ₗ[R] TensorProduct R K M :=
    LinearEquiv.rTensor M eLin
  have hcomp :
      eTensor.toLinearMap.comp (TensorProduct.mk R (R ⧸ I) M (1 : R ⧸ I)) =
        TensorProduct.mk R K M (1 : K) := by
    ext x
    simp [eTensor, eLin, eAlg, I]
  rw [← hcomp, LinearMap.ker_comp_of_ker_eq_bot]
  · simpa [I] using (LinearMap.ker_tensorProductMk (R := R) (Q := M) (I := I))
  · exact LinearMap.ker_eq_bot.mpr eTensor.injective

end LinearMap
