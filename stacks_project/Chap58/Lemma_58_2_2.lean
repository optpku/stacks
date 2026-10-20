module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisEquivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.2.2: for a field `K` with chosen separable closure `Ksep`, the geometric-fiber
functor from schemes étale over `Spec K` to discrete continuous `Gal(Ksep/K)`-sets is an
equivalence of categories. -/
@[stacks 03QR] #check
  (AlgebraicGeometry.Scheme.Etale.galoisEquivalence :
    ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
      [IsSepClosure K Ksep],
      Scheme.Etale (Spec (.of K)) ≌ DiscreteContAction TopCat.{u} Gal(Ksep/K))

@[stacks 03QR] #check
  (AlgebraicGeometry.Scheme.Etale.galoisFiberIsEquivalence :
    ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
      [IsSepClosure K Ksep],
      (AlgebraicGeometry.Scheme.Etale.galoisFiber K Ksep).IsEquivalence)
