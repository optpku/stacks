/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.ClosedImmersion

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 33.38.11: let `i : Z ⟶ X` be a closed immersion of schemes. If the underlying
topological space of `X` is Noetherian and `topologicalKrullDim X ≤ 1`, then pullback
`Pic(X) → Pic(Z)` is surjective. -/
@[stacks 09NY] #check
  (AlgebraicGeometry.Scheme.Hom.picardPullback_surjective_of_isClosedImmersion :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [TopologicalSpace.NoetherianSpace X],
      topologicalKrullDim X ≤ 1 → Function.Surjective (Scheme.Hom.picardPullback i))
