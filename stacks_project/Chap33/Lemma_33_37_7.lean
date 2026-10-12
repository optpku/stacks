/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.FractionRing.Family
import StacksCheckRecall

/-!
# Lemma 33.37.7

For a finite nonempty family of subrings of a common fraction field, use the
direct `FractionRing.SubringFamily` API.  It names the family intersection,
pairwise tensor comparisons, ring-theoretic consequences, component spectra,
their open cover, and the closed-point uniqueness statement without retaining
chapter-local aliases.
-/

universe u v

/- Lemma 33.37.7 (1): the family intersection is a domain contained in every component. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.intersection_isDomain_and_le_components :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    IsDomain (FractionRing.SubringFamily.intersection A) ∧
      ∀ i, FractionRing.SubringFamily.intersection A ≤ A i)

/- Lemma 33.37.7 (2): the family intersection is Noetherian. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.intersection_isNoetherian_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    IsNoetherianRing (FractionRing.SubringFamily.intersection A))

/- Lemma 33.37.7 (3): the family intersection is semilocal. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.intersection_finiteMaximalSpectrum_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    Finite (MaximalSpectrum (FractionRing.SubringFamily.intersection A)))

/- Lemma 33.37.7 (4): the family intersection has Krull dimension one. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.intersection_krullDim_eq_one_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    ringKrullDim (FractionRing.SubringFamily.intersection A) = 1)

/- Lemma 33.37.7 (5): every component spectrum maps to the intersection spectrum by an open
immersion. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.specComponent_isOpenImmersion_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    ∀ i, AlgebraicGeometry.IsOpenImmersion (FractionRing.SubringFamily.specComponent A i))

/- Lemma 33.37.7 (6): the open ranges of the component spectra cover the intersection
spectrum. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.specComponents_cover_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : FractionRing.SubringFamily.componentsKrullDim_eq_one A)
    (hSurj : FractionRing.SubringFamily.pairwiseTensorSurjective A),
    (⨆ i : ι,
      @AlgebraicGeometry.Scheme.Hom.opensRange _ _
        (FractionRing.SubringFamily.specComponent A i)
        (FractionRing.SubringFamily.specComponent_isOpenImmersion_of_pairwiseTensorSurjective
          A hFraction hNoetherian hSemilocal hdim hSurj i)) = ⊤)

/- Lemma 33.37.7 (7): every closed point of the intersection spectrum lies in the image of
exactly one component spectrum. -/
@[stacks 09N4]
#check (@FractionRing.SubringFamily.existsUnique_component_of_closedPoint_of_pairwiseTensorSurjective :
  ∀ {K : Type u} [Field K] {ι : Type v} (A : ι → Subring K) [Finite ι] [Nonempty ι],
    (∀ i, IsFractionRing (A i) K) →
    (∀ i, IsNoetherianRing (A i)) →
    (∀ i, Finite (MaximalSpectrum (A i))) →
    FractionRing.SubringFamily.componentsKrullDim_eq_one A →
    FractionRing.SubringFamily.pairwiseTensorSurjective A →
    ∀ x : PrimeSpectrum (FractionRing.SubringFamily.intersection A),
      x ∈ closedPoints (PrimeSpectrum (FractionRing.SubringFamily.intersection A)) →
        ∃! i : ι, x ∈ Set.range (FractionRing.SubringFamily.primeComponent A i))
