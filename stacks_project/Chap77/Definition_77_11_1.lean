/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening.Universal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Definition 77.11.1 (1): the universal flattening of a quasi-coherent `𝒪_X`-module `ℱ`
exists when the flattening functor `F_flat` of Situation 77.7.8, viewed as a functor
`(Sch/S)ᵒᵖ ⥤ Type`, is an algebraic space. -/
@[stacks 0CWR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.HasUniversalFlattening :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent], Prop)

/- Definition 77.11.1 (2): the universal flattening of `X` exists when the universal
flattening of `𝒪_X` exists. -/
@[stacks 0CWR] #check
  (AlgebraicGeometry.AlgebraicSpace.HasUniversalFlattening :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)
