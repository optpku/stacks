/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic

/-!
# Fibre components selected by a section

This module defines the point of a scheme-theoretic fibre selected by a section,
the connected component containing that point, and the union of these components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- The point of the scheme-theoretic fibre over `y` selected by a section. -/
def fiberPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) : f.fiber y :=
  (f.fiberHomeo y).symm ⟨s y, by
    change f (s y) = y
    rw [← Scheme.Hom.comp_apply, hs]
    rfl⟩

/-- The point selected in a fibre maps to the point selected by the section. -/
theorem fiberι_fiberPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) :
    f.fiberι y (fiberPoint f s hs y) = s y := sorry

/-- The image in `X` of the connected component containing the point selected
by a section in the fibre over `y`. -/
def fiberComponent {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) : Set X :=
  f.fiberι y '' connectedComponent (fiberPoint f s hs y)

/-- The point selected by a section belongs to its selected fibre component. -/
theorem section_mem_fiberComponent {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) :
    s y ∈ fiberComponent f s hs y := sorry

/-- The component selected in a fibre is contained in the corresponding
set-theoretic fibre. -/
theorem fiberComponent_subset_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) :
    fiberComponent f s hs y ⊆ f ⁻¹' {y} := sorry

/-- The component selected in the scheme-theoretic fibre is the connected
component of the section point inside the corresponding set-theoretic fibre. -/
theorem fiberComponent_eq_connectedComponentIn {X Y : Scheme.{u}}
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    fiberComponent f s hs y = connectedComponentIn (f ⁻¹' {y}) (s y) := sorry

/-- The union in `X` of the connected fibre components selected by a section. -/
def componentLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) : Set X :=
  ⋃ y : Y, fiberComponent f s hs y

/-- A point belongs to the component locus exactly when it belongs to a
selected component of some fibre. -/
theorem mem_componentLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (x : X) :
    x ∈ componentLocus f s hs ↔ ∃ y : Y, x ∈ fiberComponent f s hs y := sorry

/-- Every point selected by a section belongs to the component locus. -/
theorem section_mem_componentLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) :
    s y ∈ componentLocus f s hs := sorry

end AlgebraicGeometry.Scheme.Hom.Section
