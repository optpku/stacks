/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.LocallyFinite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u v

/- Lemma 82.9.2: In Situation 82.2.1 let `X, Y / B` be good. Let `f : X ⟶ Y` be a
morphism over `B`. If `T` is a locally finite collection of closed subsets of
`Points Y`, then `(T i).preimage (Points.continuous_map f)` is a locally finite
collection of closed subsets of `Points X`. The checked result applies to every
algebraic-space morphism, and hence to this good-over-`B` setup. -/
@[stacks 0EP6] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFinite_preimage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {I : Type v}
      (T : I → Closeds (Points Y)),
      LocallyFinite (fun i ↦ (T i : Set (Points Y))) →
        LocallyFinite
          (fun i ↦ ((T i).preimage (Points.continuous_map f) : Set (Points X))))
