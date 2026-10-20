/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Bases.Refinement
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)
variable {n : ℕ} (U : Fin (n + 2) → {V : Opens X // V ∈ B})

/- Equation 25.11.3.1: a finite intersection of basis opens is the supremum of the basis opens
contained in it. The shared theorem is generalized to an arbitrary open. -/
@[stacks 071K]
#check
  (hB.eq_iSup (⨅ k, (U k : Opens X)) :
    (⨅ k, (U k : Opens X)) =
      iSup (fun V : {V : Opens X // V ∈ B ∧ V ≤ ⨅ k, (U k : Opens X)} ↦ (V : Opens X)))

/- The same reusable basis-cover formula in set-indexed supremum form. -/
#check hB.eq_sSup
