/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
import StacksCheckRecall

/-!
# Lemma 29.35.5

Unramified and G-unramified morphisms are stable under base change.

@stack 02GA
-/

@[expose] public section

open CategoryTheory.Limits

universe u

/- Lemma 29.35.5 (1): The base change of an unramified morphism is unramified. -/
@[stacks 02GA] #check
  (AlgebraicGeometry.unramified_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Unramified f] (g : S' ⟶ S),
        AlgebraicGeometry.Unramified (pullback.snd f g))

/- Lemma 29.35.5 (2): The base change of a G-unramified morphism is G-unramified. -/
@[stacks 02GA] #check
  (AlgebraicGeometry.gUnramified_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.GUnramified f] (g : S' ⟶ S),
        AlgebraicGeometry.GUnramified (pullback.snd f g))
