/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
import StacksCheckRecall

/-!
# Lemma 29.45.2 compatibility entry point

Base-change stability of universal homeomorphisms is owned by the neutral
scheme-morphism API in `ReasLib`.
-/

@[expose] public section

/- Lemma 29.45.2: every base change of a universal homeomorphism is a
universal homeomorphism. -/
@[stacks 0CEU] #check (AlgebraicGeometry.universalHomeomorphism_isStableUnderBaseChange :
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange
    @AlgebraicGeometry.UniversalHomeomorphism)
#check @AlgebraicGeometry.UniversalHomeomorphism.pullback_snd
#check @AlgebraicGeometry.universalHomeomorphism_pullback_snd
