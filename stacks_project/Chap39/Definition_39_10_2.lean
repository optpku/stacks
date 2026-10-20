/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.GroupScheme.Action
import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable (S : Scheme.{u}) (G : Grp (Over S))

/- Definition 39.10.2: The action of `G` on `X` is free when, on every scheme of
generalized points over `S`, the induced group action is free. -/
@[stacks 07S1] #check
  (CategoryTheory.Mod.IsFree : AlgebraicGeometry.GroupScheme.Action G → Prop)

variable (X : AlgebraicGeometry.GroupScheme.Action G)

-- Freeness is cancellation for the action on every type of generalized points.
#check
  (CategoryTheory.Mod.isFree_iff X :
    CategoryTheory.Mod.IsFree X ↔
      ∀ T : Over S, IsCancelSMul (T ⟶ G.X) (T ⟶ X.X))
