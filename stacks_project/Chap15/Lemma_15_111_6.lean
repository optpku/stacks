/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints.TensorProduct

/-!
# Lemma 15.111.6

@stack 0BRG
-/

@[expose] public section

open Polynomial
open FixedPoints.Tensor
open scoped TensorProduct Algebra.TensorProduct.RightAction

universe u v w

/- Lemma 15.111.6 (current Stacks numbering: Lemma 15.112.6, tag `0BRG`):
Let `R` be a ring, let a finite group `G` act on `R`, and let `A` be an
`FixedPoints.subring R G`-algebra.  For a fixed element of
`A ⊗[FixedPoints.subring R G] R`, there is a monic
polynomial over `A` whose image in `A ⊗[FixedPoints.subring R G] R` is the
corresponding power of `T - b`.  An element of the kernel of the canonical
ambient tensor map from `A` satisfies the translated power identity in
`Polynomial A`.
-/

@[stacks 0BRG "Lemma 15.111.6 (1)"]
#check fun (R : Type u) (G : Type v) (A : Type w)
    [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] [Finite G]
  (b : fixed (R := R) (G := G) (A := A)) ↦
  (exists_monic_ambient b :
    ∃ P : Polynomial A, P.Monic ∧
      P.map (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
        baseChange (R := R) (G := G) (A := A)).toRingHom =
        (X - C (b : baseChange (R := R) (G := G) (A := A))) ^ Nat.card G)

@[stacks 0BRG "Lemma 15.111.6 (2)"]
#check fun (R : Type u) (G : Type v) (A : Type w)
    [CommRing R] [Group G] [MulSemiringAction G R]
    [CommRing A] [Algebra (FixedPoints.subring R G) A] [Finite G]
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[FixedPoints.subring R G]
      baseChange (R := R) (G := G) (A := A)).toRingHom) ↦
  (kernel_pow_ambient a :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G)
