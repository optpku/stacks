module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisFiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- A family of morphisms of étale schemes over a field is covering for the small étale
topology if and only if its maps on geometric fibers over a separable closure are jointly
surjective as maps of discrete continuous Galois sets. -/
theorem galoisFiber_ofArrows_mem_smallEtaleTopology_iff
    {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    {W : Scheme.Etale (Spec (.of K))} {ι : Type v}
    {Z : ι → Scheme.Etale (Spec (.of K))} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ smallEtaleTopology (Spec (.of K)) W ↔
      (⋃ i, Set.range
        ((forget₂ (DiscreteContAction TopCat Gal(Ksep / K)) TopCat).map
          ((galoisFiber K Ksep).map (f i)))) = Set.univ := sorry

end AlgebraicGeometry.Scheme.Etale
