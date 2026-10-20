/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 74.6.6: for a finite morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, a quasi-coherent `𝒪_X`-module `ℱ` is of finite type if and only if
`(pushforward f).obj ℱ` is of finite type as an `𝒪_Y`-module. -/
@[stacks 060Z] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isFiniteType_iff_pushforward_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ℱ.IsFiniteType ↔
        ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj ℱ).IsFiniteType)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_obj_isFiniteType_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj ℱ).IsFiniteType)
