module

public import stacks_project.Chap58.Lemma_58_6_3_GaloisFiber
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GaloisAction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

universe u

noncomputable section

#check (AlgebraicGeometry.Scheme.Etale.galoisAlgClosureToFundamentalGroup :
  ∀ (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar] [IsAlgClosed Kbar],
    Gal(Kbar/K) →* Aut ((AlgebraicGeometry.Scheme.Etale.specFieldGeometricPoint K Kbar).finiteFiber))

end
