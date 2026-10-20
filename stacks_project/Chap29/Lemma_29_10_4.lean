/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import StacksCheckRecall

/-!
# Lemma 29.10.4

Universal injectivity is stable under base change.
-/

@[expose] public section

/- Lemma 29.10.4
A base change of a universally injective morphism is universally injective.
-/
@[stacks 0472] #check
  (AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.UniversallyInjective)
