/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RepresentationTheory.Homological.ContCohomology.DiscreteCochains

@[expose] public section

universe v

open CategoryTheory
open CategoryTheory.Action.ModuleCat

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

#check (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.toTopRep G :
  DiscreteModuleCat ℤ G → TopRep.{v} ℤ G)

#check (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.toTopRepOf_V :
  ∀ X : DiscreteModuleCat ℤ G,
    (DiscreteModuleCat.toTopRepOf X).V = X.obj.V)
