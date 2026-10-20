module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Comparison

/-! # Non-equivalence of principal homogeneous spaces and fppf torsors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 110.52.1: the canonical comparison from fppf torsors to principal
homogeneous spaces is not an equivalence in general. -/
@[stacks 077B] #check
  (AlgebraicGeometry.GroupScheme.exists_principal_notEquivalent_fppfTorsors :
    ∃ (S : Scheme.{u}) (G : GroupScheme S),
      ¬ BasedFunctor.IsEquivalence
        (StackOver.Groupoids.Hom.toBasedFunctor (AlgebraicGeometry.GroupScheme.toPrincipal G)))
