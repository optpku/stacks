/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.Cancellation

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.of_comp :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Z : AlgebraicSpace S}
      (g : Y ⟶ Z) [AlgebraicGeometry.AlgebraicSpace.Etale (f ≫ g)]
      [AlgebraicGeometry.AlgebraicSpace.Etale g],
      AlgebraicGeometry.AlgebraicSpace.Etale f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Etale.instHasOfPostcompProperty :
    ∀ {S : Scheme.{u}},
      HasOfPostcompProperty
        (@AlgebraicGeometry.AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))
        (@AlgebraicGeometry.AlgebraicSpace.Etale S))
