/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Module

/-- A module sheaf, placed in degree zero, as an object of the unbounded derived category. -/
def singleDerived.{z, u, v, w} (site : RingedSite.{u, v, w})
    [UnivLE.{max u v, z}] (M : RingedSite.ModuleCat.{z} site) :
    RingedSite.Hom.ModuleDerived.{z} site :=
  (RingedSite.Hom.moduleLocalization.{z} site).obj
    ((HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{z} site) 0).obj M)

end RingedSite.Module
