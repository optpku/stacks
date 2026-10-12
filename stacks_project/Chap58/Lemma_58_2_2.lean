/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 58.2.2: for a field `K` with chosen separable closure `Ksep`, the geometric-fiber
functor from schemes étale over `Spec K` to discrete continuous `Gal(Ksep/K)`-sets is an
equivalence of categories. -/
@[stacks 03QR] #check
  (AlgebraicGeometry.Scheme.Etale.galoisFiberIsEquivalence :
    ∀ (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
      [IsSepClosure K Ksep],
      (AlgebraicGeometry.Scheme.Etale.galoisFiber K Ksep).IsEquivalence)
