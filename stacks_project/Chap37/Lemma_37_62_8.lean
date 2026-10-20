/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.8: a scheme morphism is syntomic if and only if it is flat and a local
complete-intersection morphism. -/
@[stacks 069K] #check
  (AlgebraicGeometry.Syntomic.iff_flat_and_isLocalCompleteIntersection :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Syntomic f ↔ AlgebraicGeometry.Flat f ∧
        AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)
