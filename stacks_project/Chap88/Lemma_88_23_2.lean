/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Etale
import StacksCheckRecall

/-!
# Étale morphisms of completions

If a morphism of algebraic spaces is étale, then the induced morphism of
formal completions along a closed subset is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 88.23.2: If `f : X' ⟶ X` is étale, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is étale. -/
@[stacks 0GI0] #check
  (AlgebraicGeometry.AlgebraicSpace.etale_completionAlongMap :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      [AlgebraicSpace.Etale f] (T : Closeds (Points X)),
      FormalAlgebraicSpace.Etale (completionAlong.map f T))

end AlgebraicGeometry.AlgebraicSpace
