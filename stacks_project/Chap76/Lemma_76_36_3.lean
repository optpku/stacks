/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Connected
import StacksCheckRecall

/-!
# Connectedness of geometric fibres via étale scheme neighbourhoods

The geometric fibre of a morphism of algebraic spaces over a geometric point is
connected if and only if every étale scheme neighbourhood of that point has
connected residue-field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.36.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `ybar` be a geometric point of `Y`. Then the geometric fibre
`fieldFiber f ybar.toFieldValuedPoint` is connected if and only if for every étale
neighbourhood `(V, vbar) ⟶ (Y, ybar)` with `V` a scheme, the residue-field fibre
`residueFiberOver f U.hom vbar.toScheme.image` of the base change is connected. -/
@[stacks 0A1A] #check
  (AlgebraicGeometry.AlgebraicSpace.connectedSpace_geometricFiber_iff_etaleNeighborhood :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y),
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) ↔
      ∀ (U : smallEtaleSite Y) (vbar : GeometricPoint (ofOver U.left)),
        vbar.map U.hom = ybar →
          ConnectedSpace (Points (residueFiberOver f U.hom vbar.toScheme.image)))

end AlgebraicGeometry.AlgebraicSpace
