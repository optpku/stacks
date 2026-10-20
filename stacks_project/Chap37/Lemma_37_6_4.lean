/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.BaseChange
import StacksCheckRecall

/- Lemma 37.6.4: A base change of a formally unramified morphism is formally
unramified. -/
@[stacks 02HB] #check
  (AlgebraicGeometry.FormallyUnramified.isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.FormallyUnramified)
