/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 98.25.3: a locally Noetherian scheme over a locally Noetherian base
whose restricted functor of points preserves directed affine limits is locally
of finite presentation over the base. -/
@[stacks 0GE4] #check
  (AlgebraicGeometry.Scheme.Over.locallyFinitePresentation_of_noetherianDirectedAffineLimits :
    ∀ {X S : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian X]
      (f : X ⟶ S),
      Scheme.Over.Extension.PreservesDirectedAffineLimits (Scheme.Over.locallyNoetherian S)
        ((Scheme.Over.locallyNoetherian S).ι.op ⋙ yoneda.obj (Over.mk f)) →
      LocallyOfFinitePresentation f)
