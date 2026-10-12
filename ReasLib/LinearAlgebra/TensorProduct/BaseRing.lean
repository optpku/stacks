/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Changing the base ring of a tensor product along an equivalence

If two scalar actions on the same modules correspond under a ring equivalence,
the resulting tensor products are canonically equivalent.  The equivalence is
linear over any additional scalar ring acting on the first tensor factor.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace LinearEquiv

variable {R : Type u} {S : Type v} {M : Type x}
variable [CommSemiring R] [CommSemiring S]
variable [AddCommMonoid M] [Module R M] [Module S M]

/-- The identity on a module, regarded as semilinear under a compatible ring equivalence. -/
@[stacks 0BJ5 "semilinear identity under a ring equivalence"]
def reflOfRingEquiv
    (e : R ≃+* S) (h : ∀ r : R, ∀ m : M, r • m = e r • m) :
    @LinearEquiv R S _ _ e e.symm
      (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
      M M _ _ _ _ :=
  @LinearEquiv.mk R S _ _ e e.symm
    (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
    M M _ _ _ _
    { toFun := AddEquiv.refl M
      map_add' := (AddEquiv.refl M).map_add
      map_smul' := h }
    (AddEquiv.refl M).symm (AddEquiv.refl M).left_inv (AddEquiv.refl M).right_inv

end LinearEquiv

namespace TensorProduct

variable {R : Type u} {S : Type v} {T : Type w} {M : Type x} {N : Type y}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T]
variable [AddCommMonoid M] [Module R M] [Module S M] [Module T M]
variable [AddCommMonoid N] [Module R N] [Module S N]
variable [SMulCommClass R T M] [SMulCommClass S T M]

/-- The semilinear tensor equivalence underlying a change of base ring. -/
@[stacks 0BJ5 "semilinear tensor product base-ring equivalence"]
def baseRingSemilinearEquiv
    (e : R ≃+* S)
    (hM : ∀ r : R, ∀ m : M, r • m = e r • m)
    (hN : ∀ r : R, ∀ n : N, r • n = e r • n) :
    @LinearEquiv R S _ _ e e.symm
      (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
      (M ⊗[R] N) (M ⊗[S] N) _ _ _ _ :=
  @TensorProduct.congr R S _ _ e M N M N _ _ _ _ _ _ _ _ e.symm
    (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
    (LinearEquiv.reflOfRingEquiv e hM) (LinearEquiv.reflOfRingEquiv e hN)

/-- The underlying change-of-base tensor equivalence commutes with an additional scalar action
on the first tensor factor. -/
@[stacks 0BJ5 "semilinear tensor base change commutes with extra scalars"]
theorem baseRingSemilinearEquiv_map_smul
    (e : R ≃+* S)
    (hM : ∀ r : R, ∀ m : M, r • m = e r • m)
    (hN : ∀ r : R, ∀ n : N, r • n = e r • n)
    (t : T) (x : M ⊗[R] N) :
    baseRingSemilinearEquiv e hM hN (t • x) =
      t • baseRingSemilinearEquiv e hM hN x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Change the base ring of a tensor product along a ring equivalence whose actions agree on
both tensor factors. -/
@[stacks 0BJ5 "tensor product base-ring equivalence"]
noncomputable def baseRingEquiv
    (e : R ≃+* S)
    (hM : ∀ r : R, ∀ m : M, r • m = e r • m)
    (hN : ∀ r : R, ∀ n : N, r • n = e r • n) :
    M ⊗[R] N ≃ₗ[T] M ⊗[S] N :=
  (@LinearEquiv.toAddEquiv R S _ _ e e.symm
    (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
    (M ⊗[R] N) (M ⊗[S] N) _ _ _ _
    (baseRingSemilinearEquiv e hM hN)).toLinearEquiv
      (baseRingSemilinearEquiv_map_smul e hM hN)

/-- Changing the base ring leaves pure tensors unchanged. -/
@[stacks 0BJ5 "tensor product base-ring equivalence on pure tensors", simp]
theorem baseRingEquiv_tmul
    (e : R ≃+* S)
    (hM : ∀ r : R, ∀ m : M, r • m = e r • m)
    (hN : ∀ r : R, ∀ n : N, r • n = e r • n)
    (m : M) (n : N) :
    baseRingEquiv (T := T) e hM hN (m ⊗ₜ n) = m ⊗ₜ n := rfl

/-- The inverse change-of-base equivalence also leaves pure tensors unchanged. -/
@[stacks 0BJ5 "inverse tensor product base-ring equivalence on pure tensors", simp]
theorem baseRingEquiv_symm_tmul
    (e : R ≃+* S)
    (hM : ∀ r : R, ∀ m : M, r • m = e r • m)
    (hN : ∀ r : R, ∀ n : N, r • n = e r • n)
    (m : M) (n : N) :
    (baseRingEquiv (T := T) e hM hN).symm (m ⊗ₜ n) = m ⊗ₜ n := by
  apply (baseRingEquiv (T := T) e hM hN).injective
  simp

end TensorProduct
