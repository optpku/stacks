module

public import ReasLib.AlgebraicGeometry.ChowMotive.Additive
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe u

/- Lemma 45.4.6 -/
@[stacks 0FGF] #check
  (ChowMotive.instHasFiniteBiproducts :
    ∀ (k : Type u) [Field k],
      HasFiniteBiproducts
        (ChowMotive k (fun _ => AlgebraicGeometry.Correspondence.GradedCategory k)))
