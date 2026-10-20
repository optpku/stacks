/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonal Localizations of Separable Field Extensions

This leaf records the localization form of the diagonal multiplication of a
separable algebraic field extension. The statement retains the canonical
tensor-product map rather than exposing auxiliary denominators from a
particular proof.

@stack 0C2X
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.IsSeparable

/-- Lemma 10.43.8, tag `0C2X`: for a separable algebraic field extension
`K / k`, tensor-square multiplication `K ⊗[k] K → K` is a localization at a
submonoid of its source. -/
@[stacks 0C2X]
theorem exists_lmul_isLocalization
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] :
    ∃ S : Submonoid (K ⊗[k] K), S.IsLocalizationMap (TensorProduct.lmul' k) := sorry

end Algebra.IsSeparable
