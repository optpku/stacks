/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
import StacksCheckRecall

/-!
# Base change of universally injective morphisms of algebraic spaces

The base change of a universally injective morphism of algebraic spaces by any
morphism of algebraic spaces is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.19.5 -/
@[stacks 03MW] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyInjective_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.UniversallyInjective S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
