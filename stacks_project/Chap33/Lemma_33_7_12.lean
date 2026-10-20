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

/- Lemma 33.7.12 (Tag 038C): if the Galois base change of the source is connected
and that of the target is disconnected, then the target is disconnected. -/
@[stacks 038C]
#check (AlgebraicGeometry.GeometricallyConnected.Galois.ConnectedSource.not_target :
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {T X : AlgebraicGeometry.Scheme.{u}}
    (t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (x : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (f : T ⟶ X) (h_over : f ≫ x = t)
    (hTK : ConnectedSpace (AlgebraicGeometry.FieldExtension.baseChange k K t))
    (hXK : ¬ ConnectedSpace (AlgebraicGeometry.FieldExtension.baseChange k K x)),
    ¬ ConnectedSpace X)

end
