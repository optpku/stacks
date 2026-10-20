/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.GrpTopCat.Limits
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/- Lemma 5.30.3: the reusable category-theoretic owner is `Grp TopCat`; its three source clauses
are supplied by the ReasLib limits API and its concrete forgetful bridges. -/
@[stacks 0B20 "limits of topological groups"]
#check (inferInstance : HasLimits (Grp TopCat.{u}))

@[stacks 0B20 "limits commute with the forgetful functor to topological spaces"]
#check (inferInstance : PreservesLimits (Grp.forget TopCat.{u}))

@[stacks 0B20 "limits commute with the forgetful functor to groups"]
#check (inferInstance : PreservesLimits (forget₂ (Grp TopCat.{u}) GrpCat.{u}))
