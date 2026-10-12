/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.Neighborhood

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry Topology

universe u

/- Lemma 37.29.5: for a flat finitely presented morphism with a section and a
geometrically reduced fibre over `y`, the component locus is a neighbourhood of
the section-selected component of that fibre. -/
@[stacks 055Q]
#check (AlgebraicGeometry.Scheme.Hom.Section.componentLocus_mem_nhdsSet :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (y : Y) [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
    [AlgebraicGeometry.Flat f]
    [AlgebraicGeometry.GeometricallyReduced (f.fiberToSpecResidueField y)],
    AlgebraicGeometry.Scheme.Hom.Section.componentLocus f s hs ∈
      𝓝ˢ (AlgebraicGeometry.Scheme.Hom.Section.fiberComponent f s hs y))
