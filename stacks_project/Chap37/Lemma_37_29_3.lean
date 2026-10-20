/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.Shrinking

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.29.3: for a finite-type morphism with a section and a point `y`,
there is a nonempty open of the reduced closure of `y` whose base change makes
the inverse image of the section-selected component locus open and closed. -/
@[stacks 055N] #check
  (AlgebraicGeometry.Scheme.Hom.Section.exists_open_pointClosure_componentLocus_isClopen :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
      (hs : s ≫ f = 𝟙 Y) [AlgebraicGeometry.Scheme.Hom.FiniteType f] (y : Y),
      ∃ V : (AlgebraicGeometry.Scheme.PointClosure.scheme y).Opens, Nonempty V ∧
        IsClopen
          ((pullback.fst f (V.ι ≫ AlgebraicGeometry.Scheme.PointClosure.ι y)) ⁻¹'
            AlgebraicGeometry.Scheme.Hom.Section.componentLocus f s hs))
