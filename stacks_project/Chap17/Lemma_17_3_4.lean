/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

/- Lemma 17.3.4: if `j : U ⟶ X` is an open immersion, then lower shriek
`j_! : Ab(U) ⥤ Ab(X)` is exact. -/
@[stacks 01AK]
#check fun {X U : TopCat.{u}} {j : U ⟶ X}
    (hj : Topology.IsOpenEmbedding j) ↦
  (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.exact hj :
    exactFunctor (U.Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.ExtensionByInitial.OpenEmbedding.functor hj))
