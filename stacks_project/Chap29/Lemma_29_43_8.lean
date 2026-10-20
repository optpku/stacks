/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.43.8: a base change of an H-projective morphism is H-projective. -/
@[stacks 01WF] #check
  (AlgebraicGeometry.HProjective.pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.HProjective f → ∀ g : S' ⟶ S,
        AlgebraicGeometry.HProjective (CategoryTheory.Limits.pullback.snd f g))
