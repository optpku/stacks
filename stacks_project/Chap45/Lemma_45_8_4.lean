/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FieldExtension.AlgebraicPullback

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup.FieldExtension

/- Lemma 45.8.4: for an algebraic field extension `K / k` and a finite-type `k`-scheme `X`,
the kernel of the map `CH_i(X) → CH_i(X_K)` is torsion. -/
@[stacks 0FH8]
#check (AlgebraicGeometry.ChowGroup.FieldExtension.algebraicExtensionPullback_ker_isTorsion :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ),
    AddMonoid.IsTorsion (algebraicExtensionPullback k K X i).ker)
