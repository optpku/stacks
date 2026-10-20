/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.48.8: in a commutative triangle of morphisms of algebraic spaces
over a scheme `S`, if `Y ⟶ Z` is smooth and `X ⟶ Z` is a local complete
intersection morphism, then `f : X ⟶ Y` is a local complete intersection
morphism. -/
@[stacks 0CHL] #check
  (AlgebraicGeometry.AlgebraicSpace.isLocalCompleteIntersection_of_smooth_of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      AlgebraicGeometry.AlgebraicSpace.etaleLocal @AlgebraicGeometry.Smooth g →
      AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection (f ≫ g) →
      AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection f)
