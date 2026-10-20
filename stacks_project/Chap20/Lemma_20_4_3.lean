/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Cohomology
public import ReasLib.Topology.Sheaf.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace CategoryTheory

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (H : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-
Lemma 20.4.3 (02FQ): for an abelian sheaf `H` on a topological space, the canonical map
from isomorphism classes of `H`-torsors to `H.H 1` is bijective.

This is the opens-site specialization of the reusable site-level classification map.
-/
@[stacks 02FQ "torsors on a topological space classified by first cohomology"] #check
  (Sheaf.Torsor.Cohomology.classMap_bijective H :
    Function.Bijective (Sheaf.Torsor.Cohomology.classMap H))

#check (Sheaf.Torsor.Cohomology.classMap H :
  Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups H) → H.H 1)

#check (Sheaf.Torsor.Cohomology.classMap_trivial H :
  Sheaf.Torsor.Cohomology.classMap H
      (_root_.Quotient.mk'' (Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups H))) = 0)

end CategoryTheory
