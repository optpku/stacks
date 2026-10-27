/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EnlargedGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSections

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.isGrothendieckAbelian_moduleCat_spacesRingedSite :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (AlgebraicGeometry.AlgebraicSpace.spacesRingedSite X)))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.isGrothendieckAbelian_moduleCat_etaleTotalRingedSite :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)),
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)))
