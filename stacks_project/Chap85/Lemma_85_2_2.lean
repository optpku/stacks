/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Sheaves.Simplicial.System

/-! Lemma 85.2.2: sheaves on a simplicial Zariski site are equivalent to compatible sheaf systems. -/

open CategoryTheory
open scoped Simplicial

universe u

/- Lemma 85.2.2 -/
@[stacks 09VM] #check (CategoryTheory.SimplicialObject.sheafEquivalence (C := Type u) :
  (X : SimplicialObject TopCat.{u}) →
    Sheaf (CategoryTheory.SimplicialObject.zariskiTopology X) (Type u) ≌
      TopCat.Sheaf.InverseLimit.SheafSystem.asCategory (C := Type u) (F := X))
