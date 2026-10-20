/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits CommRingCat
open AlgebraicGeometry

universe u

/- Definition 33.7.1: A scheme over a field is geometrically connected if every base change to a
field extension is connected. -/
@[stacks 0362] #check (AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_baseChange :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)),
    AlgebraicGeometry.GeometricallyConnected f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace ((pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme)))
