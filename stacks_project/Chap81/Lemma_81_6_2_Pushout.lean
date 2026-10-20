/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Thickening
import StacksCheckRecall

/-!
# Pushouts of algebraic spaces along a thickening and an affine morphism

A thickening and an affine morphism of algebraic spaces over a scheme `S` admit a
pushout in `AlgebraicSpace S`, and the canonical (and any isomorphic) morphism
`Y ⟶ Y ⨿_X X'` is a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 81.6.2: a thickening and an affine morphism of algebraic spaces over a
scheme admit a pushout. -/
@[stacks 07VX] #check
  (AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening.instHasPushout :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f], HasPushout i f)
