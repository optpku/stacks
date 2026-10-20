/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
import StacksCheckRecall

/-!
# Smooth morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.37.5: A smooth morphism of algebraic spaces is locally of finite
presentation. -/
@[stacks 04AJ] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_smooth :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Smooth f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f)
