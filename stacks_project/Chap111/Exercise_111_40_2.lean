/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.40.2 (1): an invertible 𝒪_X-module on a scheme X is quasi-coherent. -/
@[stacks 02AE] #check
  (AlgebraicGeometry.Scheme.Modules.instIsQuasicoherentOfRankOne :
    ∀ {X : Scheme.{u}} (L : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank 1 L],
      L.IsQuasicoherent)

/- Exercise 111.40.2 (2): if `f : X ⟶ Y` is a morphism of locally ringed spaces and `L` is an
invertible `𝒪_Y`-module, then `f^* L` is an invertible `𝒪_X`-module. -/
@[stacks 02AE] #check
  (AlgebraicGeometry.LocallyRingedSpace.Modules.pullback_isFiniteLocallyFreeOfRank_one :
    ∀ {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (L : Y.Modules)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u} 1 L],
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u} 1
        ((RingedSpace.Hom.pullback f.toShHom).obj L))
