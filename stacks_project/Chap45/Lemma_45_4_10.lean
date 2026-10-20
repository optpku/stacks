module

public import ReasLib.AlgebraicGeometry.ChowMotive.LeftDualizable
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 45.4.10 -/
@[stacks 0FGJ] #check (ChowMotive.isLeftDualizable : ∀ {k : Type u} [Field k] (M : ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)), CategoryTheory.IsLeftDualizable M)
