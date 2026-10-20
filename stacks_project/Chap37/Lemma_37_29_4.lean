/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.Constructible

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.29.4: for a finitely presented morphism with a section, the union
of fibre components meeting that section is locally constructible in the source. -/
@[stacks 055P] #check
  (AlgebraicGeometry.Scheme.Hom.Section.componentLocus_isLocallyConstructible :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
      (hs : s ≫ f = 𝟙 Y) [AlgebraicGeometry.Scheme.Hom.FinitePresentation f],
      Topology.IsLocallyConstructible
        (AlgebraicGeometry.Scheme.Hom.Section.componentLocus f s hs))
