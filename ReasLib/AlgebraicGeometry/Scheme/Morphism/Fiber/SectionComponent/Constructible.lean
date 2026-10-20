/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.Topology.Constructible

/-!
# Local constructibility of fibre components selected by a section
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- For a morphism of finite presentation with a section, the union of fibre
components meeting the section is locally constructible in the source. -/
theorem componentLocus_isLocallyConstructible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) [Scheme.Hom.FinitePresentation f] :
    Topology.IsLocallyConstructible (componentLocus f s hs) := sorry

end AlgebraicGeometry.Scheme.Hom.Section
