/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_14_3_System
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

/- Lemma 85.14.3 (1): in Situation 85.3.3, with a sheaf of rings O on C_total, given
K_0 in D(O_0) and an isomorphism α : Lf_{δ 1}^* K_0 ≅ Lf_{δ 0}^* K_0 in D(O_1)
satisfying the cocycle condition, the objects K_n = Lf_{τ^n_n}^* K_0 together with
the source comparison maps K_φ form a cartesian simplicial system of the derived
category of modules. -/
@[stacks 0GMF] #check @DerivedModuleSystem.ofCocycle

/- Lemma 85.14.3 (2): the system constructed from (K_0, α) is cartesian. -/
@[stacks 0GMF] #check @DerivedModuleSystem.ofCocycle_isCartesian
