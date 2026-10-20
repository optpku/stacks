/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Geometrically connected fibre loci

This module defines the locus where the geometric fibres of a scheme morphism
are connected and records its invariance under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus in the target of a scheme morphism where its fibres are geometrically connected. -/
def geometricallyConnectedFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  {y | GeometricallyConnected (f.fiberToSpecResidueField y)}

/-- Membership in the geometrically connected fibre locus is geometric connectedness of the
corresponding fibre over the residue field. -/
theorem mem_geometricallyConnectedFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    y ∈ f.geometricallyConnectedFiberLocus ↔
      GeometricallyConnected (f.fiberToSpecResidueField y) := sorry

/-- Geometric connectedness of a fibre is preserved and reflected by a pullback square of
scheme morphisms. -/
theorem geometricallyConnectedFiber_iff_of_isPullback {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (y' : Y') :
    GeometricallyConnected (f'.fiberToSpecResidueField y') ↔
      GeometricallyConnected (f.fiberToSpecResidueField (g y')) := sorry

/-- The geometrically connected fibre locus of a base-changed scheme morphism is the inverse
image of the original locus. -/
theorem geometricallyConnectedFiberLocus_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.geometricallyConnectedFiberLocus = g ⁻¹' f.geometricallyConnectedFiberLocus := sorry

end AlgebraicGeometry.Scheme.Hom
