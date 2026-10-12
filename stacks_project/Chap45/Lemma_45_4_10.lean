/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.LeftDualizable
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 45.4.10 -/
@[stacks 0FGJ] #check (ChowMotive.isLeftDualizable : ∀ {k : Type u} [Field k] (M : ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)), CategoryTheory.IsLeftDualizable M)
