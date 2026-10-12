/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Right-Oriented Tensor-Product Maps

This leaf owns the tensor-product map induced by a scalar tower when the
unchanged tensor factor is written on the right.
-/

@[expose] public section

universe u v w

open scoped TensorProduct Algebra.TensorProduct.Right

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

section

/-- The canonical right-tensor algebra map induced by a scalar tower `R → Q → S`. -/
noncomputable def tensor_right_map {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    Q ⊗[R] T →ₐ[T] S ⊗[R] T :=
  (Algebra.TensorProduct.commRight R T S).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R Q S)).comp
      (Algebra.TensorProduct.commRight R T Q).symm.toAlgHom)

/-- Compute `tensor_right_map` on a pure tensor. -/
@[simp]
theorem tensor_right_map_tmul {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T]
    (q : Q) (t : T) :
    tensor_right_map (R := R) (S := S) (Q := Q) (T := T) (q ⊗ₜ[R] t) =
      (algebraMap Q S q) ⊗ₜ[R] t := sorry

/-- The algebra structure induced by `tensor_right_map` extends the original `Q`-algebra map. -/
theorem tensor_right_map_q_tower {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    (letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensor_right_map (R := R) (S := S) (Q := Q) (T := T)).toAlgebra
    (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp (algebraMap Q (Q ⊗[R] T)) =
      algebraMap Q (S ⊗[R] T)) := sorry

/-- The algebra structure induced by `tensor_right_map` fixes the right tensor inclusion. -/
theorem tensor_right_map_includeRight_comp {Q : Type*} [CommRing Q] [Algebra R Q]
    [Algebra Q S] [IsScalarTower R Q S] {T : Type w} [CommRing T] [Algebra R T] :
    (letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensor_right_map (R := R) (S := S) (Q := Q) (T := T)).toAlgebra
    (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) := sorry

end

end Algebra
