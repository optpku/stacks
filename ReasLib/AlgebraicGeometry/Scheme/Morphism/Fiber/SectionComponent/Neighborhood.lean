/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.Topology.NhdsSet

/-!
# Neighbourhoods of fibre components selected by a section
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- For a flat finitely presented morphism with a section and a geometrically
reduced fibre, the component locus is a neighbourhood of the section-selected
component of that fibre. -/
theorem componentLocus_mem_nhdsSet {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) [Scheme.Hom.FinitePresentation f] [Flat f]
    [GeometricallyReduced (f.fiberToSpecResidueField y)] :
    componentLocus f s hs ∈ 𝓝ˢ (fiberComponent f s hs y) := sorry

/-- For a flat finitely presented morphism with geometrically reduced fibres,
the locus formed by the connected components of fibres meeting a section is open. -/
theorem isOpen_componentLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) [Scheme.Hom.FinitePresentation f] [Flat f]
    [GeometricallyReduced f] : IsOpen (componentLocus f s hs) := sorry

end AlgebraicGeometry.Scheme.Hom.Section
