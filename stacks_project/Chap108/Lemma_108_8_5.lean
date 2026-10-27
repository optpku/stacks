/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Smooth
import StacksCheckRecall

/-!
# Lemma 108.8.5

If `f : X ⟶ B` is flat, proper, and of finite presentation and has relative
dimension at most `1`, then the structure morphism of the Picard stack over `B`
is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

/- Lemma 108.8.5: the Picard structure morphism is smooth in relative dimension
at most one for a flat, proper morphism of finite presentation. -/
@[stacks 0DPJ] #check (AlgebraicGeometry.AlgebraicSpace.Picard.toBase.smooth :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [Flat f] → [FinitePresentation f] → [Proper f] → [RelativeDimensionLE f 1] →
      CohStack.Hom.Smooth (Picard.toBase f))
