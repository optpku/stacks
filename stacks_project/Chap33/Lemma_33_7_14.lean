/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.ResidueField

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 33.7.14 (1): a connected scheme over a field is geometrically connected
when the ground field is algebraically closed in the residue field of a point. -/
@[stacks 04KV]
#check
  (AlgebraicGeometry.GeometricallyConnected.ResidueField.of_connectedSpace_of_groundAlgebraicClosure_eq_bot :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)),
      ConnectedSpace X → ∀ x : X,
        Scheme.Hom.ResidueField.algebraicClosureOfSpec f x = ⊥ →
          GeometricallyConnected f)

/- Lemma 33.7.14 (2): a connected scheme over a field with a rational point is
geometrically connected. -/
@[stacks 04KV]
#check
  (AlgebraicGeometry.GeometricallyConnected.ResidueField.of_connectedSpace_of_isIsoMap :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)),
      ConnectedSpace X → ∀ (x : X) [IsIso (f.residueFieldMap x)],
        GeometricallyConnected f)

end
