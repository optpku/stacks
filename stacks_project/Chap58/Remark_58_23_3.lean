module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Remark 58.23.3 (1): if `(A, m)` is a complete local Noetherian ring, `f ∈ m`
is nonzero, `A_f` is `(S₂)`, and every irreducible component of `Spec A` has
dimension at least `4`, then restriction
`colim_{U₀ ⊂ U' ⊂ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence. -/
@[stacks 0BLW]
#check (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_S2_dim4 :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [hf : Fact ((f : A) ≠ 0)]
    [SerreConditionS (Localization.Away (f : A)) 2]
    [hdim : Fact (∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
      (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
    Functor.IsEquivalence (principalNeighborhoodRestriction f t))

/- Remark 58.23.3 (2): the same restriction is an equivalence in particular
when `A` is a normal domain of dimension at least `4`. -/
@[stacks 0BLW]
#check (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_normal_dim4 :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [hf : Fact ((f : A) ≠ 0)]
    [IsDomain A] [IsIntegrallyClosed A]
    [hdim : Fact ((4 : WithBot ℕ∞) ≤ ringKrullDim A)]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
    Functor.IsEquivalence (principalNeighborhoodRestriction f t))

end AlgebraicGeometry.PuncturedSpectrum
