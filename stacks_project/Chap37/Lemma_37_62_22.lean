/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Unramified
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.62.22 (1): a local complete-intersection morphism is unramified if and only if it
is formally unramified. -/
@[stacks 06B9] #check
  (AlgebraicGeometry.LocallyOfType.unramified_iff_formallyUnramified :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfType RingHom.IsLocalCompleteIntersection f],
      Unramified f ↔ FormallyUnramified f)

/- Lemma 37.62.22 (2): for a formally unramified local complete-intersection morphism,
its conormal sheaf represented by any universal first-order thickening is finite locally free. -/
@[stacks 06B9] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalSheaf_isFiniteLocallyFree :
    ∀ {Y : Scheme.{u}} (T : Thickening.Over Y)
      [FormallyUnramified T.left.hom]
      [LocallyOfType RingHom.IsLocalCompleteIntersection T.left.hom]
      [Thickening.IsUniversalFirstOrder T],
      Scheme.Modules.IsFiniteLocallyFree
        (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.conormalSheaf T))
