/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Differentials.Transitivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.11.11: for composable scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ S`,
formal smoothness of `f` makes the canonical transitivity complex
`f^* Ω[Y/S] ⟶ Ω[X/S] ⟶ Ω[X/Y]` short exact. -/
@[stacks 06B6] #check
  (AlgebraicGeometry.FormallySmooth.relativeDifferentialsTransitivity_shortExact :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.FormallySmooth f],
      (AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.complex
        f.toShHom g.toShHom).ShortExact)
