/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.28.4: a surjective finite locally free morphism of algebraic spaces
over a scheme transfers the resolution property from its source to its target. -/
@[stacks 0GUV] #check
  (AlgebraicGeometry.AlgebraicSpace.hasResolutionProperty_of_surjective_finiteLocallyFree :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree f],
      SheafOfModules.HasResolutionProperty
        (AlgebraicGeometry.AlgebraicSpace.structureSheaf X) →
        SheafOfModules.HasResolutionProperty
          (AlgebraicGeometry.AlgebraicSpace.structureSheaf Y))
