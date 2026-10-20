/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAction.FixedPoints

@[expose] public section

/-!
# Invariant-theoretic consequences for a tensor-product action

The right-factor action and its fixed subalgebra are defined independently of
invariance.  Under `Algebra.IsInvariant S B G`, coefficients of the finite
orbit polynomial descend through `S`; the resulting orbit-polynomial and
kernel statements are recorded here.  Shift-power and integrality consequences
live in the sibling `...Invariant.TensorProduct.ShiftPower` leaf.  The extra
`FaithfulSMul S B` hypothesis is kept on kernel results because invariance alone
does not make `algebraMap S B` injective.
@stack 0BRG
-/

open Polynomial
open Algebra.TensorProduct.RightAction
open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w x

namespace Algebra.IsInvariant.TensorProduct

variable {S : Type u} {A : Type v} {B : Type w} {G : Type x}
variable [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S A] [Algebra S B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G S B]
variable [Finite G] [Algebra.IsInvariant S B G]

/-- The orbit power of a fixed tensor element has coefficients lifted from `A`. -/
@[stacks 0BRG "fixed tensor orbit power lies in polynomial lifts"]
theorem pow_mem_lifts
    (b : fixedSubalgebra (S := S) (A := A) (B := B) (G := G)) :
    ((X - C b) ^ Nat.card G : Polynomial
      (fixedSubalgebra (S := S) (A := A) (B := B) (G := G))) ∈
      Polynomial.lifts (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom := sorry
-- Proof strategy: install `Fintype.ofFinite G` and present `A` by a multivariable polynomial
-- algebra over `S`.  The induced evaluation `MvPolynomial A B → A ⊗[S] B` is a surjective
-- equivariant ring hom.  Lift `b`, apply the finite-orbit polynomial construction, and use
-- `Algebra.IsInvariant.charpoly_mem_lifts` coefficientwise to descend the fixed presentation from
-- `B` to `S`; evaluating the descended coefficients in `A` gives membership in the displayed
-- `Polynomial.lifts` subsemiring.

/-- A fixed tensor element admits a monic polynomial over the left factor. -/
@[stacks 0BRG "fixed tensor orbit polynomial"]
theorem exists_monic
    (b : fixedSubalgebra (S := S) (A := A) (B := B) (G := G)) :
    ∃ P : Polynomial A, P.Monic ∧
      P.map (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom =
        (X - C b) ^ Nat.card G := sorry
-- Proof strategy: apply `Polynomial.lifts_and_natDegree_eq_and_monic` to `pow_mem_lifts b` and
-- the monicity of `(X - C b) ^ Nat.card G`; retain only the lifted monic polynomial and its map
-- equation.

variable [FaithfulSMul S B]

/-- A kernel element of the canonical fixed-tensor map satisfies the orbit-power identity. -/
@[stacks 0BRG "kernel power identity for invariant tensor base change"]
theorem kernel_pow
    (a : RingHom.ker (toFixed (S := S) (A := A) (B := B) (G := G)).toRingHom) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry
-- Proof strategy: use the same polynomial presentation as `pow_mem_lifts`.  Transport `a` through
-- the quotient presentation of `A`; the vanishing of `toFixed a` puts the transported class in
-- the fixed-points quotient kernel, where `FixedPoints.Quotient.kernel_pow` gives the translated
-- power identity.  Descend it through the presentation equivalence; `FaithfulSMul S B` supplies
-- the injectivity needed for the coefficient comparison.

/-- Predicate form of the invariant tensor kernel-power identity. -/
@[stacks 0BRG "kernel power identity from fixed-tensor map vanishing"]
theorem kernel_pow_of_eq_zero {a : A}
    (ha : toFixed (S := S) (A := A) (B := B) (G := G) a = 0) :
    ((X - C a) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := sorry
-- Proof strategy: package `a` and `ha` as an element of the ring-hom kernel and apply
-- `kernel_pow`.

end Algebra.IsInvariant.TensorProduct
