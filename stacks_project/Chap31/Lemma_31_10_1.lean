/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Lemma 31.10.1: for a locally finite type morphism of schemes, the Fitting ideal sheaves of
relative differentials commute with arbitrary base change. -/
@[stacks 0C3I] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_pullback :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (g : S' ⟶ S) (i : ℕ),
      (Scheme.fittingIdealSheaf (Ω[f.toShHom]) i).comap (pullback.fst f g) =
        Scheme.fittingIdealSheaf (Ω[(pullback.snd f g).toShHom]) i)
