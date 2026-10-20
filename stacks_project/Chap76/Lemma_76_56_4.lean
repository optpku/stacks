/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Ideal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.56.4: In Situation 76.56.1, the algebraic space `X` has the
resolution property if and only if `(Modules.pushforward sit.π).obj sit.I.toModule`
is a quotient of a finite locally free `𝒪_X`-module. -/
@[stacks 0GV1] #check
  (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent.hasResolutionProperty_iff_epi_pushforward_ideal :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (sit : ResolutionDescent X),
      SheafOfModules.HasResolutionProperty (structureSheaf X) ↔
        ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
          (q : E ⟶ (Modules.pushforward sit.π).obj sit.I.toModule),
          Epi q)
