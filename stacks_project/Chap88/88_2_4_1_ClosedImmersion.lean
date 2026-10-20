module

public import ReasLib.RingTheory.AdicCompletion.ClosedImmersion

universe u

open scoped TensorProduct

/- The migrated declarations remain available through the shared owner. -/
#check (AdicCompletion.closedImmersionBaseChange :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (a : Ideal A) (Ibar : Ideal (A ⧸ a))
    [h_complete : IsAdicComplete
      (Ibar.map (algebraMap (A ⧸ a) (B ⧸ a.map (algebraMap A B))))
      (B ⧸ a.map (algebraMap A B))],
    AdicCompletion (AdicCompletion.tensorIncludeRightIdeal B a Ibar)
        (B ⊗[A] (A ⧸ a)) ≃ₐ[A ⧸ a] B ⧸ a.map (algebraMap A B))
