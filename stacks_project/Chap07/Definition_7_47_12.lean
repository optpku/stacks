/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Canonical.Representable

import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 7.47.12: the finest topology on a category such that all representable
presheaves are sheaves is the canonical topology. Its finest-topology property
means that it is greatest among all topologies satisfying this sheaf condition. -/
@[stacks 00ZA] #check (CategoryTheory.Sheaf.isGreatest_canonicalTopology C :
  IsGreatest {J : GrothendieckTopology C | ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)}
    (CategoryTheory.Sheaf.canonicalTopology C))

#check (CategoryTheory.Sheaf.canonicalTopology C : GrothendieckTopology C)

variable (X : C)

#check (CategoryTheory.Sheaf.isSheaf_yoneda_obj X :
  Presieve.IsSheaf (CategoryTheory.Sheaf.canonicalTopology C) (yoneda.obj X))
