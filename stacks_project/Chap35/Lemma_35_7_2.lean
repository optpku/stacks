/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.FiniteType.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.7.2: finite type of a module sheaf descends along an open, surjective,
flat morphism of locally ringed spaces. -/
@[stacks 09UB] #check
  (AlgebraicGeometry.LocallyRingedSpace.Hom.isFiniteType_of_pullback :
    ∀ {X Y : AlgebraicGeometry.LocallyRingedSpace.{u}} (f : X ⟶ Y) (ℱ : Y.Modules)
      (h_open : IsOpenMap f.base) (h_surjective : Function.Surjective f.base)
      [RingedSpace.Hom.IsFlat f.toShHom]
      [((AlgebraicGeometry.RingedSpace.Hom.pullback f.toShHom).obj ℱ).IsFiniteType],
      ℱ.IsFiniteType)
