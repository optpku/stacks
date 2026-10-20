/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Invertible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules TopologicalSpace

universe u

variable {X : LocallyRingedSpace.{u}} (L : X.Modules)

/- Definition 111.40.1 (1): on a locally ringed space `X`, an invertible `𝒪_X`-module is a sheaf
of `𝒪_X`-modules `L` that is locally isomorphic to `𝒪_U` on a neighborhood of every point. -/
@[stacks 02AD] #check (SheafOfModules.IsFiniteLocallyFreeOfRank 1 L : Prop)

/- Definition 111.40.1 (2): an `𝒪_X`-module `L` is trivial if it is isomorphic to `𝒪_X` as an
`𝒪_X`-module. -/
@[stacks 02AD] #check (AlgebraicGeometry.RingedSpace.IsTrivial L : Prop)

#check IsFiniteLocallyFreeOfRank.iff_exists_neighborhood 1 L
#check @SheafOfModules.unit
#check @SheafOfModules.unit_isFiniteLocallyFreeOfRankOne
#check @RingedSpace.unit_isTrivial
#check @RingedSpace.rankOne_iff_isInvertible
