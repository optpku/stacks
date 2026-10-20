/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.Descent

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.7.13 (Tag 056R): a geometrically connected source and connected target
over a field give a geometrically connected target. -/
@[stacks 056R]
#check
  (AlgebraicGeometry.GeometricallyConnected.Descent.of_connectedTarget :
    ∀ {k : Type u} [Field k] {T X : AlgebraicGeometry.Scheme.{u}}
      (t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (x : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (f : T ⟶ X) (h_over : f ≫ x = t)
      (hT : AlgebraicGeometry.GeometricallyConnected t) (hX : ConnectedSpace X),
      AlgebraicGeometry.GeometricallyConnected x)

end
