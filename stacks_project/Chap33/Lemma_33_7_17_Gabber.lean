/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.ConnectedComponents

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.7.17 (Gabber): the projection from a field-extension base change maps each connected
component onto a connected component of the original scheme. -/
@[stacks 04PZ] #check
  (AlgebraicGeometry.FieldExtension.Connected.image_component_eq :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (x : AlgebraicGeometry.FieldExtension.baseChange k K f),
      (AlgebraicGeometry.FieldExtension.toSource k K f).base '' connectedComponent x =
        connectedComponent ((AlgebraicGeometry.FieldExtension.toSource k K f).base x))
