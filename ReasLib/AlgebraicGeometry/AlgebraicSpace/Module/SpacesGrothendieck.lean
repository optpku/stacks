/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EtaleDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Native module sheaves on the spaces-étale site form a Grothendieck abelian category. -/
instance spacesModulesIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u} (RingedSite.ModuleCat.{u} (spacesRingedSite X)) := sorry

end AlgebraicGeometry.AlgebraicSpace
