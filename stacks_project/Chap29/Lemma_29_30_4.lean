/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability

@[expose] public section

universe u

/-!
# Lemma 29.30.4

This chapter entry is a compatibility facade for base-change stability of
syntomic scheme morphisms.
-/

/- Lemma 29.30.4: The base change of a morphism which is syntomic is syntomic. -/
@[stacks 01UI] #check
  (AlgebraicGeometry.syntomic_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Syntomic f → ∀ (g : S' ⟶ S),
        AlgebraicGeometry.Syntomic (CategoryTheory.Limits.pullback.snd f g))
