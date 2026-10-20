/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap41.Definition_41_3_5
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.3.6: for a locally finite-type morphism to a locally Noetherian scheme,
the local-ring and affine-neighborhood notions of being unramified at a point agree. -/
@[stacks 039J] #check
  (AlgebraicGeometry.Scheme.Hom.unramifiedAt_iff_localRingCriterion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
      [LocallyOfFiniteType f] (x : X),
      f.UnramifiedAt x ↔ MaximalIdealResidueFieldUnramifiedAtCriterion f x)
