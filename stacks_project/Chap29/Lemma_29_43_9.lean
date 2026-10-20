/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.9 (1): a base change of a projective morphism is projective. -/
@[stacks 02V6] #check (AlgebraicGeometry.Projective.pullback_snd :
  {X S S' : AlgebraicGeometry.Scheme.{u}} → {f : X ⟶ S} →
    AlgebraicGeometry.Projective f → (g : S' ⟶ S) →
      AlgebraicGeometry.Projective (CategoryTheory.Limits.pullback.snd f g))

/- Lemma 29.43.9 (2): a base change of a locally projective morphism is locally projective. -/
@[stacks 02V6] #check (AlgebraicGeometry.LocallyProjective.pullback_snd :
  {X S S' : AlgebraicGeometry.Scheme.{u}} → {f : X ⟶ S} →
    AlgebraicGeometry.LocallyProjective f → (g : S' ⟶ S) →
      AlgebraicGeometry.LocallyProjective (CategoryTheory.Limits.pullback.snd f g))
