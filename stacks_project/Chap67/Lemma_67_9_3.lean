/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
import StacksCheckRecall

/-!
# Base change of universally closed morphisms of algebraic spaces

The base change of a universally closed morphism of algebraic spaces by any
morphism of algebraic spaces is universally closed.
-/

universe u

/- Lemma 67.9.3: The base change of a universally closed morphism of algebraic
spaces by any morphism of algebraic spaces is universally closed. -/
@[stacks 03IS] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyClosed_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.UniversallyClosed S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
