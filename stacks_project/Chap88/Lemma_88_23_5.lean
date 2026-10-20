/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.QuasiCompact
import StacksCheckRecall

/-!
# Quasi-compact morphisms of completions

If a morphism of algebraic spaces is quasi-compact, then the induced morphism
of formal completions along a closed subset is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 88.23.5: If `f : X' ⟶ X` is quasi-compact, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is quasi-compact. -/
@[stacks 0GDE] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiCompact_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.QuasiCompact f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.ReductionData.QuasiCompact
        (completionAlong.reductionData X' (T.preimage (Points.continuous_map f)))
        (completionAlong.reductionData X T) (completionAlong.map f T))

end AlgebraicGeometry.AlgebraicSpace
