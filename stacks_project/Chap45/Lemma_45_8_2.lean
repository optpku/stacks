/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FieldExtension.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FieldExtension
  AlgebraicGeometry.ChowGroup.FieldExtension

noncomputable section

universe u

/- Lemma 45.8.2: for an algebraic extension `K / k` and a finite-type `k`-scheme `X`,
`CH_i(X_K) = colim CH_i(X_{k'})` over the subextensions `K / k' / k` with `k' / k` finite.
This is the special case of Stacks 0FVQ (`ChowLimit.chowCocone_isColimit`) for the inverse
system of spectra of finite intermediate fields. -/
@[stacks 0FH6]
#check (AlgebraicGeometry.ChowGroup.FieldExtension.finiteIntermediateChowCocone_isColimit :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ)
    [Algebra.IsAlgebraic k K],
    Nonempty (IsColimit (finiteIntermediateChowCocone k K X i)))
