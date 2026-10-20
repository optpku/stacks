/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 76.56.3: In Situation 76.56.1, assume `X` is Noetherian. Then `X` has
  the resolution property if and only if `π_* I` is the quotient of a finite
  locally free `𝒪_X`-module. -/
@[stacks 0GV0] #check
  (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent.hasResolutionProperty_iff_pushforward_ideal :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian X]
      (sit : AlgebraicGeometry.AlgebraicSpace.ResolutionDescent X),
      SheafOfModules.HasResolutionProperty
          (AlgebraicGeometry.AlgebraicSpace.structureSheaf X) ↔
        ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
          (q : E ⟶
            (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward sit.π).obj
              sit.I.toModule),
          CategoryTheory.Epi q)
