/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAction.FixedPoints
public import ReasLib.RingTheory.Invariant.FixedPoints
public import ReasLib.RingTheory.Invariant.TensorProduct

@[expose] public section

/-!
# Fixed-subring specialization of the invariant tensor API

The reusable tensor action, fixed subalgebra, coefficient-lifting, and kernel
infrastructure live in the generic `Algebra.TensorProduct.RightAction` and
`Algebra.IsInvariant.TensorProduct` leaves.  This file keeps the short
fixed-subring names used by Chapter 15 as thin source-facing bridges.

@stack 0BRG
-/

open Polynomial
open Algebra.TensorProduct.RightAction
open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w

namespace FixedPoints.Tensor

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

/-- The canonical base-change tensor product over the fixed-point subring. -/
@[stacks 0BRG "fixed-point tensor base change",
  stacks 0BRH "fixed-point tensor base change"]
abbrev baseChange := A ⊗[FixedPoints.subring R G] R

/-- The fixed subalgebra of the canonical fixed-point base change. -/
@[stacks 0BRG "fixed tensor subalgebra",
  stacks 0BRH "fixed subalgebra after tensor base change"]
noncomputable abbrev fixed :=
  fixedSubalgebra (S := FixedPoints.subring R G) (A := A) (B := R) (G := G)

/-- The canonical map from `A` to the fixed tensor subalgebra. -/
@[stacks 0BRG "canonical fixed-points map",
  stacks 0BRH "Lemma 15.111.7 canonical map"]
noncomputable def fixedPointsMap : A →ₐ[FixedPoints.subring R G]
    fixed (R := R) (G := G) (A := A) :=
  toFixed (S := FixedPoints.subring R G) (A := A) (B := R) (G := G)

/-- The specialized fixed-points map has the expected underlying tensor value. -/
@[simp, stacks 0BRG "fixed-point map value"]
theorem fixedPointsMap_apply (a : A) :
    (fixedPointsMap (R := R) (G := G) (A := A) a : baseChange (R := R) (G := G) (A := A)) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
        baseChange (R := R) (G := G) (A := A)) a := sorry
-- Proof strategy: unfold `fixedPointsMap`, `fixed`, and `baseChange`, then apply
-- `Algebra.TensorProduct.RightAction.coe_toFixed`.

/-- The specialized fixed-points map followed by subtype inclusion is `includeLeft`. -/
@[simp, stacks 0BRG "fixed-point map composition"]
theorem fixedPointsMap_val_comp :
    (fixed (R := R) (G := G) (A := A)).val.comp
        (fixedPointsMap (R := R) (G := G) (A := A)) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
        baseChange (R := R) (G := G) (A := A)) := sorry
-- Proof strategy: unfold the three specialization abbreviations and use
-- `Algebra.TensorProduct.RightAction.val_comp_toFixed`.

variable [Finite G]

/-- Lemma 15.111.6 (1), with the source-facing ambient tensor codomain. -/
@[stacks 0BRG "Lemma 15.111.6 (1), ambient fixed tensor orbit polynomial"]
theorem exists_monic_ambient (b : fixed (R := R) (G := G) (A := A)) :
    ∃ P : Polynomial A, P.Monic ∧
      P.map (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
        baseChange (R := R) (G := G) (A := A)).toRingHom =
        (X - C (b : baseChange (R := R) (G := G) (A := A))) ^ Nat.card G := sorry
-- Proof strategy: obtain the canonical fixed-subalgebra identity from
-- `Algebra.IsInvariant.TensorProduct.exists_monic`, using
-- `FixedPoints.subring_isInvariant`.  Map that identity through the fixed-subalgebra subtype and
-- simplify `Polynomial.map_map` with `fixedPointsMap_val_comp`.

/-- A fixed tensor element has a monic orbit polynomial over `A`. -/
@[stacks 0BRG "Lemma 15.111.6 (1), fixed tensor orbit polynomial"]
theorem exists_monic (b : fixed (R := R) (G := G) (A := A)) :
    ∃ P : Polynomial A, P.Monic ∧
      P.map (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom =
        (X - C b) ^ Nat.card G := sorry
-- Proof strategy: unfold the fixed-subring specialization and apply
-- `Algebra.IsInvariant.TensorProduct.exists_monic` with the canonical
-- `FixedPoints.subring_isInvariant` instance.

/-- A kernel element has the translated power identity in `Polynomial A`. -/
@[stacks 0BRG "Lemma 15.111.6 (2), kernel power identity"]
theorem kernel_pow
    (a : RingHom.ker ((fixedPointsMap (R := R) (G := G) (A := A)).toRingHom)) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry
-- Proof strategy: specialize `Algebra.IsInvariant.TensorProduct.kernel_pow` to
-- `S = FixedPoints.subring R G` and `B = R`; the subtype algebra map supplies the canonical
-- `FaithfulSMul` instance.

/-- Lemma 15.111.6 (2), with the source-facing ambient tensor kernel. -/
@[stacks 0BRG "Lemma 15.111.6 (2), ambient tensor kernel power identity"]
theorem kernel_pow_ambient
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
      baseChange (R := R) (G := G) (A := A)).toRingHom) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry
-- Proof strategy: use `Algebra.TensorProduct.RightAction.ker_toFixed` to transport `a` to the
-- kernel of `fixedPointsMap`, apply `kernel_pow`, and retain the same underlying element of `A`.

/-- Predicate form of the fixed-subring kernel power identity. -/
@[stacks 0BRG "kernel power identity from map vanishing"]
theorem kernel_pow_of_map_eq_zero {a : A}
    (ha : fixedPointsMap (R := R) (G := G) (A := A) a = 0) :
    ((X - C a) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry
-- Proof strategy: package `a` with `ha` as a kernel element and apply `kernel_pow`.

end FixedPoints.Tensor
