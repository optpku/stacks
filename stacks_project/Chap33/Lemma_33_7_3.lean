/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 33.7.3: geometric connectedness is invariant under extension of the ground field. -/
@[stacks 054N] #check
  (AlgebraicGeometry.GeometricallyConnected.BaseChange.iff_fieldExtension :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k))
      {K : Type u} [Field K] [Algebra k K],
      GeometricallyConnected f ↔
        GeometricallyConnected (FieldExtension.toBase k K f))
