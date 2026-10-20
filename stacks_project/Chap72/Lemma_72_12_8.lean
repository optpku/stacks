/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Connected.FiniteSeparable
import StacksCheckRecall

/-!
# Finite-separable test for geometric connectedness of algebraic spaces

An algebraic space over a field `k` is geometrically connected if and only if its
base change to every finite separable field extension of `k` is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected

/- Lemma 72.12.8: Let `k` be a field. Let `X` be an algebraic space over `k`.
Then `X` is geometrically connected if and only if for every finite separable
field extension `K/k`, the algebraic space obtained by base change of `X` along
`FieldExtension.specMap k K` is connected. -/
@[stacks 0A17]
#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.iff_finiteSeparable :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
        [Algebra.IsSeparable k K],
        ConnectedSpace (Points (baseChange (FieldExtension.specMap k K) X)))

end AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected
