/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Krull dimension under field-extension base change

This leaf owns the finite-type affine base-change equality used by relative
dimension arguments. The statement is independent of a chosen polynomial
normalization presentation.
-/

open scoped TensorProduct

namespace Algebra.FiniteType

universe u v w

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]
variable [hSFiniteType : Algebra.FiniteType k S]
variable {K : Type w} [Field K] [Algebra k K]

include hSFiniteType
/-- Lemma 10.116.5, tag 00P3: Krull dimension of a finite-type `k`-algebra is unchanged after
base change to an arbitrary field extension `K / k`. -/
@[stacks 00P3 "Krull dimension under field-extension base change"]
theorem ringKrullDim_tensorProduct_eq_of_fieldExtension :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := sorry

end Algebra.FiniteType
