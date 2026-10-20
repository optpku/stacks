module

public import ReasLib.AlgebraicGeometry.ChowMotive.Additive

@[expose] public section

open CategoryTheory.Limits

universe u

#check
  (ChowMotive.instHasFiniteBiproducts :
    ∀ (k : Type u) [Field k],
      HasFiniteBiproducts
        (ChowMotive k (fun _ => AlgebraicGeometry.Correspondence.GradedCategory k)))
