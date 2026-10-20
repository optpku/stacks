/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Krull Dimension After Field Extension

@stack 00P3
-/

open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable {K : Type w} [Field K] [Algebra k K]

/- Lemma 10.116.5: extending the ground field does not change the Krull
dimension of a finite-type algebra. -/
@[stacks 00P3]
#check
  (Algebra.FiniteType.ringKrullDim_tensorProduct_eq_of_fieldExtension
    (k := k) (S := S) (K := K) :
      ringKrullDim S = ringKrullDim (K ⊗[k] S))
