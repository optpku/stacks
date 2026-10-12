/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisFiber.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/- Remark 58.2.3: under the correspondence of Lemma 58.2.2, covering families in the
small étale site of `Spec K` correspond to jointly surjective families of maps of discrete
continuous `Gal(Ksep/K)`-sets. -/
@[stacks 03QS] #check
  (AlgebraicGeometry.Scheme.Etale.galoisFiber_ofArrows_mem_smallEtaleTopology_iff :
    ∀ {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
      {W : Scheme.Etale (Spec (.of K))} {ι : Type v}
      {Z : ι → Scheme.Etale (Spec (.of K))} (f : ∀ i, Z i ⟶ W),
      Sieve.ofArrows Z f ∈ smallEtaleTopology (Spec (.of K)) W ↔
        (⋃ i, Set.range
          ((forget₂ (DiscreteContAction TopCat Gal(Ksep / K)) TopCat).map
            ((galoisFiber K Ksep).map (f i)))) = Set.univ)

end AlgebraicGeometry.Scheme.Etale
