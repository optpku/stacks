/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Maximum
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.76.5: the fibre integral of a weighting of a locally quasi-finite morphism with
quasi-compact source attains its maximum. -/
@[stacks 0F3K] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.exists_isGreatest_fiberIntegral :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [CompactSpace X] [Nonempty Y] {w : X → ℤ},
      f.IsWeighting w →
        ∃ d : ℤ, IsGreatest
          (Set.range (f.fiberIntegral
            (AlgebraicGeometry.Scheme.Hom.tendstoCofinite_of_compactSource f) w)) d)
