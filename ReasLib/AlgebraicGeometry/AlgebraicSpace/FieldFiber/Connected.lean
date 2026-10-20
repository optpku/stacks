/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

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

/-- The geometric fibre of a morphism of algebraic spaces over a geometric point
is connected if and only if the residue-field fibre over every pointed étale
scheme neighbourhood of that geometric point is connected. -/
@[stacks 0A1A]
theorem connectedSpace_geometricFiber_iff_etaleNeighborhood
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) ↔
      ∀ (U : smallEtaleSite Y) (vbar : GeometricPoint (ofOver U.left)),
        vbar.map U.hom = ybar →
          ConnectedSpace (Points (residueFiberOver f U.hom vbar.toScheme.image)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
