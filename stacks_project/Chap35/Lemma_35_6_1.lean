module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Galois

open CategoryTheory

universe u

/- Lemma 35.6.1: for a finite Galois extension `K/k` and a `k`-scheme `X`,
restriction identifies quasi-coherent modules on `X` with Galois descent systems
on its base change to `K`. -/
@[stacks 0CDR] #check
  (@AlgebraicGeometry.Scheme.QCoh.Galois.restriction.isEquivalence :
    ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsGalois k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)),
      (AlgebraicGeometry.Scheme.QCoh.Galois.restriction k K f).IsEquivalence)
