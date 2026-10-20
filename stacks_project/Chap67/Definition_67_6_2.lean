/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
import StacksCheckRecall

@[expose]
public section

universe u

/- Definition 67.6.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is open if the map of topological spaces `|X| ⟶ |Y|` is open. -/
@[stacks 03Z2] #check (AlgebraicGeometry.AlgebraicSpace.Open :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))

/- Definition 67.6.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally open if for every morphism `Z ⟶ Y` of algebraic spaces the map
`|Z ×_Y X| ⟶ |Z|` is open, i.e. the base change `Z ×_Y X ⟶ Z` is open. -/
@[stacks 03Z2] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S))
