/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
import StacksCheckRecall

@[expose]
public section

universe u

/- Definition 67.53.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is a universal homeomorphism iff for every morphism `Z ⟶ Y` of algebraic
spaces the base change `Z ×_Y X ⟶ Z` induces a homeomorphism
`|Z ×_Y X| ⟶ |Z|`. -/
@[stacks 05Z5] #check (AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
