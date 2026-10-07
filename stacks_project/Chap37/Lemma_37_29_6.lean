module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.Neighborhood

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.29.6: for a flat finitely presented morphism with geometrically
reduced fibres, the component locus selected by a section is open. -/
@[stacks 055R] #check
  (AlgebraicGeometry.Scheme.Hom.Section.isOpen_componentLocus :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
      (hs : s ≫ f = 𝟙 Y) [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.GeometricallyReduced f],
      IsOpen (AlgebraicGeometry.Scheme.Hom.Section.componentLocus f s hs))
