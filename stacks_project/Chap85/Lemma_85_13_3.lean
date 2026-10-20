/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_13_3_System
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites

/- Lemma 85.13.3 (1): in Situation 85.3.3, given K_0 in D(C_0) and an isomorphism
α : f_{δ 1}⁻¹ K_0 ≅ f_{δ 0}⁻¹ K_0 in D(C_1) satisfying the cocycle condition,
the objects K_n = f_{τ^n_n}⁻¹ K_0 together with the source comparison maps K_φ
form a cartesian simplicial system of the derived category. -/
@[stacks 0GME] #check @ofCocycle

/- Lemma 85.13.3 (2): the system constructed from (K_0, α) is cartesian. -/
@[stacks 0GME] #check @ofCocycle_isCartesian
