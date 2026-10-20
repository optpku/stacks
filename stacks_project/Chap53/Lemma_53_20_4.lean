/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
import StacksCheckRecall

/- Lemma 53.20.4: An at-worst-nodal morphism of relative dimension one remains
at worst nodal after arbitrary base change. -/
@[stacks 0C5B] #check
  (AlgebraicGeometry.AtWorstNodal.baseChange :
    ∀ {X S S' : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.AtWorstNodal f],
      AlgebraicGeometry.AtWorstNodal
        (CategoryTheory.Limits.pullback.snd f g))
