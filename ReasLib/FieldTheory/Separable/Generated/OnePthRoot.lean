/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot
public import ReasLib.FieldTheory.Separable.Generated.Frobenius

/-!
# Separability and the first Frobenius-root extension

This leaf owns the reusable field-extension criteria in characteristic `p`.
The coordinate-level tensor arguments used to prove them belong to the
source-facing chapter; only their mathematical interfaces are exported here.

@stack 030W
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.IsSeparableOver

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Lemma 10.44.2 (Tag 030W): in characteristic `p`, separability is equivalent to preservation
of linear independence by the `p`th-power map on finite subsets. -/
@[stacks 030W]
theorem iff_linearIndepOn_pow
    {p : ℕ} [Fact p.Prime] [CharP k p] :
    IsSeparableOver k K ↔
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) →
          LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := sorry

namespace OnePthRoot

/-- Reducedness of the first Frobenius-root base change implies the Frobenius linear-independence
criterion for the extension. -/
@[stacks 030W]
theorem linearIndepOn_pow
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsReduced (K ⊗[k] IntermediateField.onePthRootExtension k p)] :
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := sorry

/-- Explicit-hypothesis form of `linearIndepOn_pow`; use this bridge when
the reducedness fact is proposition-valued data rather than an installed instance. -/
@[stacks 030W "explicit reducedness bridge"]
theorem linearIndepOn_pow_of
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (hred : IsReduced (K ⊗[k] IntermediateField.onePthRootExtension k p)) :
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := sorry

/-- Lemma 10.44.2 (Tag 030W): separability is equivalent to reducedness after tensoring with the
concrete first Frobenius-root extension. -/
@[stacks 030W]
theorem iff_isReduced
    {p : ℕ} [Fact p.Prime] [CharP k p] :
    IsSeparableOver k K ↔
      IsReduced (K ⊗[k] IntermediateField.onePthRootExtension k p) := sorry

end OnePthRoot

end Algebra.IsSeparableOver
