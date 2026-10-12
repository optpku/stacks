/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor presentation of a quotient by a mapped ideal

This leaf identifies `N / (IS)N` with `N tensor[R] R/I`.  The construction is independent of
flatness and associated primes, so those theories can share one scalar-accurate quotient model.

The scoped right tensor-product algebra instance is used only to compose the canonical
intermediate equivalences.  It does not add an instance parameter to the public API.

@stack 0312
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace Ideal.Quotient.Map

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- Quotienting an `S`-module by the action of the extension of `I` agrees, `S`-linearly, with
tensoring by `R / I`. -/
@[stacks 0312 "mapped-ideal quotient as a tensor product"]
noncomputable def quotientEquivTensor (I : Ideal R) :
    (N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N))) ≃ₗ[S]
      N ⊗[R] (R ⧸ I) :=
  (TensorProduct.quotTensorEquivQuotSMul N (I.map (algebraMap R S))).symm.trans <|
    (TensorProduct.congr (Ideal.qoutMapEquivTensorQout (R := R) (S := S) (I := I))
      (LinearEquiv.refl S N)).trans <|
    (TensorProduct.comm S _ N).trans <|
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (R ⧸ I)

/-- `quotientEquivTensor` sends a quotient representative to the corresponding tensor with
`1 : R / I`. -/
@[simp, stacks 0312 "mapped-ideal quotient tensor equivalence on representatives"]
theorem quotientEquivTensor_apply_mk (I : Ideal R) (n : N) :
    quotientEquivTensor (R := R) (S := S) I (Submodule.Quotient.mk n) =
      n ⊗ₜ[R] (1 : R ⧸ I) := sorry

/-- The inverse tensor presentation sends `n tensor 1` to the quotient class of `n`. -/
@[simp, stacks 0312 "inverse mapped-ideal quotient tensor equivalence on generators"]
theorem quotientEquivTensor_symm_apply_tmul_one (I : Ideal R) (n : N) :
    (quotientEquivTensor (R := R) (S := S) I).symm (n ⊗ₜ[R] (1 : R ⧸ I)) =
      Submodule.Quotient.mk n := by
  apply (quotientEquivTensor (R := R) (S := S) I).injective
  simp

end Ideal.Quotient.Map
