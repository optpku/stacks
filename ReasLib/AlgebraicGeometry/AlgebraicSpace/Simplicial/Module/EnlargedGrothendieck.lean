/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Module sheaves on the spaces-étale site at coefficient universe `u + 1`
form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_moduleCat_spacesRingedSite (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  sorry

/-- Module sheaves on the total spaces-étale site at coefficient universe `u + 1`
form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_moduleCat_etaleTotalRingedSite
    (U : SimplicialObject (AlgebraicSpace S)) :
    IsGrothendieckAbelian.{u + 1} (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial
