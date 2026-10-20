/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible.QuasiSeparated
import StacksCheckRecall

/-!
# Étale-local and topological constructibility on quasi-separated algebraic spaces

For a quasi-separated algebraic space, étale-local constructibility of a subset of `|X|`
is equivalent to local constructibility in the topological space of points.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.8.7: Let `S` be a scheme. Let `X` be a quasi-separated algebraic space over `S`.
Let `E ⊂ |X|` be a subset. Then `E` is étale locally constructible if and only if `E` is a
locally constructible subset of the topological space `|X|`. -/
@[stacks 0ECZ]
#check (AlgebraicGeometry.AlgebraicSpace.isEtaleLocallyConstructible_iff_isLocallyConstructible :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (E : Set (Points X)),
    IsEtaleLocallyConstructible E ↔ Topology.IsLocallyConstructible E)
