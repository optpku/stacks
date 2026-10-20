/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import StacksCheckRecall

/- Lemma 37.11.3: A base change of a formally smooth morphism is formally smooth. -/
@[stacks 02H2] #check
  (AlgebraicGeometry.FormallySmooth.instIsStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.FormallySmooth)
