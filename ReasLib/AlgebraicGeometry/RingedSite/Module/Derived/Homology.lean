/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic

/-! # Native homology of derived module sheaves -/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.NativeDerived

universe z u v w

/-- Integer-degree homology of derived module sheaves, with their native abelian structure. -/
def homologyFunctor (X : RingedSite.{u, v, w}) [Abelian (ModuleCat.{z} X)] (n : ℤ) :
    category.{z} X ⥤ ModuleCat.{z} X :=
  @DerivedCategory.homologyFunctor _ _ (abelian X) (hasDerivedCategory X) n

end RingedSite.NativeDerived
