/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Bases
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

variable {X : Type u}

/- The generated topology is already owned by mathlib. -/
#check TopologicalSpace.generateFrom

/- Lemma 5.5.5: a family `B` of subsets determines the topology `generateFrom B`. Expressing the
datum directly is more useful than the tautological package `∃! t, t = generateFrom B`. -/
@[stacks 08ZJ]
#check (fun B : Set (Set X) ↦ (generateFrom B : TopologicalSpace X))
