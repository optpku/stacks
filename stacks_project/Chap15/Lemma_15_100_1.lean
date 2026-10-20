/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Restriction

@[expose] public section

/-!
# Lemma 15.100.1

@stack 0E1W

Lemma 15.100.1 (Stacks `0E1W`) recalls the canonical mixed base-change identification
`RHom_R(K, M) ≃ RHom_R' (K ⊗ᴸ[R] R', M)` for a ring map `R → R'`, `K ∈ D(R)`, and
`M ∈ D(R')`.  Here both sides are compared in `D(R)`: the left side views `M` by restriction of
scalars, while the right side restricts the canonical `R'`-linear `RHom` object.
-/

@[stacks 0E1W "Lemma 15.100.1"]
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.Restriction.comparisonIso

/- The corresponding natural isomorphism in the variable `M`. -/
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.Restriction.comparisonNatIso
