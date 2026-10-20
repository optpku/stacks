/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.ConnectedComponents
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.7.15: for a field extension `K/k` and a `k`-scheme `X`, the inverse image
of every connected component of `X` is a union of connected components of `X_K`. -/
@[stacks 04PY] #check
  (AlgebraicGeometry.FieldExtension.Connected.preimage_component_isConnectedComponentSaturated :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) (C : ConnectedComponents X),
      Set.IsConnectedComponentSaturated
        ((AlgebraicGeometry.FieldExtension.toSource k K f).base ⁻¹' C.set))
