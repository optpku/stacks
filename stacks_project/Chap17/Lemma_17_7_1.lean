/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.OpenClosed
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

/- Lemma 17.7.1 (1): for an open subset `U ⊆ X` and its closed complement, the canonical
sequence `j_! j^{-1} F ⟶ F ⟶ i_* i^{-1} F` is short exact. -/
@[stacks 02UT "(1)"]
#check fun {X : TopCat.{u}}
    (U : Opens X) (F : X.Sheaf AddCommGrpCat.{u}) ↦
  (TopCat.Sheaf.OpenClosed.shortExact U F :
    ((TopCat.Sheaf.OpenClosed.sequence U).obj F).ShortExact)

/- Lemma 17.7.1 (2): the canonical open-closed short exact sequence is functorial in `F`. -/
@[stacks 02UT "(2)"]
#check fun {X : TopCat.{u}}
    (U : Opens X) {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) ↦
  ((TopCat.Sheaf.OpenClosed.sequence U).map f :
    (TopCat.Sheaf.OpenClosed.sequence U).obj F ⟶
      (TopCat.Sheaf.OpenClosed.sequence U).obj G)
