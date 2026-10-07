module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import stacks_project.Chap58.Lemma_58_23_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AffineAlgebraizationSetup
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.PuncturedSpectrum

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (f : IsLocalRing.maximalIdeal A)

/-- Remark 58.23.3 (1): if `(A, m)` is a complete local Noetherian ring, `f ∈ m`
is nonzero, `A_f` is `(S₂)`, and every irreducible component of `Spec A` has
dimension at least `4`, then `finiteEtaleNeighborhoodRestriction` identifying
`colim_{U₀ ⊂ U' ⊂ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence. -/
@[stacks 0BLW]
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_S2_dim4
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [h_dualizing :
      Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    [hf : Fact ((f : A) ≠ 0)]
    [SerreConditionS (Localization.Away (f : A)) 2]
    [hdim :
      Fact
        (∀ p : PrimeSpectrum A,
          p.asIdeal ∈ minimalPrimes A →
            (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))]
    (t :
      ColimitCocone
        (finiteEtaleNeighborhoodDiagram
          (idealOnOpen
            (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property)))) :
    Functor.IsEquivalence
      (finiteEtaleNeighborhoodRestriction
        (idealOnOpen
          (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property))
        t) := sorry

/-- Remark 58.23.3 (2): the conclusion of Remark 58.23.3 (1) holds in particular
when `A` is a normal domain of dimension at least `4`. -/
@[stacks 0BLW]
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_normal_dim4
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [h_dualizing :
      Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    [hf : Fact ((f : A) ≠ 0)]
    [IsDomain A] [IsIntegrallyClosed A]
    [hdim : Fact ((4 : WithBot ℕ∞) ≤ ringKrullDim A)]
    (t :
      ColimitCocone
        (finiteEtaleNeighborhoodDiagram
          (idealOnOpen
            (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property)))) :
    Functor.IsEquivalence
      (finiteEtaleNeighborhoodRestriction
        (idealOnOpen
          (ofPrincipal (IsLocalRing.maximalIdeal A) (f : A) f.property))
        t) := sorry

end AlgebraicGeometry.PuncturedSpectrum
