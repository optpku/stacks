/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.ConnectedComponent

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.8.17 (1) (Tag 054S): finitely many geometrically irreducible canonical
irreducible components imply finitely many connected components. -/
@[stacks 054S]
#check (@AlgebraicGeometry.GeometricallyIrreducible.Components.finiteConnectedComponents :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [Finite (irreducibleComponents X)]
    (hgeom : GeometricallyIrreducible.Components.all f),
      Finite (ConnectedComponents X))

/- Lemma 33.8.17 (2) (Tag 054S): under the same hypotheses, every canonical connected component
is geometrically connected. -/
@[stacks 054S]
#check (@AlgebraicGeometry.GeometricallyConnected.Components.of_geometricallyIrreducible :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [Finite (irreducibleComponents X)]
    (hgeom : GeometricallyIrreducible.Components.all f)
    (C : ConnectedComponents X),
      GeometricallyConnected.Components.isConnected f C)

end
