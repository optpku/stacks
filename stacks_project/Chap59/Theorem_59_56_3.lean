module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.StalkGaloisSet
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

@[expose] public section

universe u

/- Theorem 59.56.3: Taking stalks at any geometric point of a field spectrum induces
an equivalence between étale sheaves of sets and discrete continuous Galois sets. -/
@[stacks 03QT] #check (AlgebraicGeometry.Scheme.Etale.stalkGaloisSet_isEquivalence :
  ∀ (K : Type u) [Field K] (s : GeometricPoint (Spec (.of K))),
    (stalkGaloisSet K s).IsEquivalence)
