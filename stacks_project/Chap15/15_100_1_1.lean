/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.ScalarExtension

@[expose] public section

/-!
# Equation 15.100.1.1

@stack 0E1X

Equation 15.100.1.1 (Stacks `0E1X`) is the source-facing comparison
`RHom_R(K, M) ⊗ᴸ[R] R' ⟶ RHom_R' (K ⊗ᴸ[R] R', M ⊗ᴸ[R] R')` attached to Lemma 15.100.1.
The canonical `RHom.BaseChange.ScalarExtension.comparison` is the coherent bifunctor
transformation, and `comparisonApp` is precisely its component at `(K, M)`.
-/

@[stacks 0E1X "15.100.1.1 scalar-extension RHom comparison"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparisonApp

/- The comparison is natural in both derived arguments. -/
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.comparison
