/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Regular morphisms of schemes

This file defines regular morphisms of schemes and records their component properties.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A scheme morphism is regular at `x` when it is flat at `x` and its residue-field
fibre is geometrically regular at the distinguished point `f.asFiber x`. -/
def RegularAt (f : X ⟶ Y) (x : X) : Prop :=
  f.flatAt x ∧
    IsGeometricallyRegularAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)

/-- Pointwise regularity is equivalent to pointwise flatness together with geometric
regularity of the residue-field fibre at its distinguished point. -/
theorem regularAt_iff (f : X ⟶ Y) (x : X) :
    f.RegularAt x ↔ f.flatAt x ∧
      IsGeometricallyRegularAt (f.fiberToSpecResidueField (f x)) (f.asFiber x) := sorry

namespace RegularAt

/-- A scheme morphism that is regular at a point is flat there. -/
theorem flatAt {f : X ⟶ Y} {x : X} (h : f.RegularAt x) :
    f.flatAt x := sorry

/-- At a point where a scheme morphism is regular, its residue-field fibre is
geometrically regular at the distinguished point. -/
theorem isGeometricallyRegularAt {f : X ⟶ Y} {x : X} (h : f.RegularAt x) :
    IsGeometricallyRegularAt
      (f.fiberToSpecResidueField (f x)) (f.asFiber x) := sorry

end RegularAt
end Scheme.Hom

/-- A scheme morphism is regular when it is flat and its fibres are geometrically regular
over their residue fields. -/
class Regular {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- A regular morphism is flat. -/
  flat : Flat f
  /-- Every fibre of a regular morphism is geometrically regular over the residue field. -/
  isGeometricallyRegular_fiber :
    ∀ y : Y, Scheme.Hom.IsGeometricallyRegular (f.fiberToSpecResidueField y)

namespace Regular

variable {X Y : Scheme.{u}}

/-- Regularity is equivalent to flatness together with geometrically regular fibres. -/
theorem iff (f : X ⟶ Y) :
    Regular f ↔ Flat f ∧
      (∀ y : Y, Scheme.Hom.IsGeometricallyRegular (f.fiberToSpecResidueField y)) := sorry

/-- A regular scheme morphism is canonically flat. -/
instance instFlat (f : X ⟶ Y) [Regular f] : Flat f := sorry

/-- A regular scheme morphism is regular at every source point. -/
theorem regularAt (f : X ⟶ Y) [Regular f] (x : X) :
    f.RegularAt x := sorry

end Regular

/-- A scheme morphism with locally Noetherian fibres is regular exactly when it is
regular at every source point. -/
theorem regular_iff_forall_regularAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)] :
    Regular f ↔ ∀ x : X, f.RegularAt x := sorry

end AlgebraicGeometry
