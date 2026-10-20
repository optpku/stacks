/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.LeftDualizable
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 45.4.10 -/
@[stacks 0FGJ] #check (ChowMotive.isLeftDualizable : ∀ {k : Type u} [Field k] (M : ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)), CategoryTheory.IsLeftDualizable M)
