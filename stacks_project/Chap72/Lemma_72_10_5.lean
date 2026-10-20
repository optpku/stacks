/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.PurelyTranscendental
import StacksCheckRecall

universe u

/- Lemma 72.10.5

Let `k` be a field and `X` a quasi-separated algebraic space over `k`. If there
exists a purely transcendental field extension `K/k` such that `X_K` is a
scheme, then `X` is a scheme. The explicit-extension criterion below gives this
existential formulation by eliminating its extension witness.
-/
@[stacks 0B85] #check (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_isScheme_baseChange_isPurelyTranscendental : ∀ {k K : Type u} [Field k] [Field K] [Algebra k K], _root_.FieldExtension.IsPurelyTranscendental k K → ∀ (X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated X], AlgebraicGeometry.AlgebraicSpace.IsScheme (AlgebraicGeometry.AlgebraicSpace.baseChange (AlgebraicGeometry.FieldExtension.specMap k K) X) → AlgebraicGeometry.AlgebraicSpace.IsScheme X)
