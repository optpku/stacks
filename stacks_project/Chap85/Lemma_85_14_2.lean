/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_14_2_System
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

/- Lemma 85.14.2 (1): in Situation 85.3.3, with a sheaf of rings O on C_total, an
object K of D(O) yields the simplicial system (K_n, K(φ)) of the derived category of
modules, with K_n = Lg_n^* K and K(φ) : Lf_φ^* K_m ⟶ K_n. -/
@[stacks 0D9P] #check @toDerivedModuleSystem

/- Lemma 85.14.2 (2): if K is cartesian, so is that system. -/
@[stacks 0D9P] #check @instIsCartesian_toDerivedModuleSystem
