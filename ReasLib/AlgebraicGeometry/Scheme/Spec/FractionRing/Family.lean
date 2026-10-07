module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Spec.FractionRing.DimensionOne
public import ReasLib.RingTheory.Localization.FractionRing.SubringFamily

/-!
# Spectra of finite families of fraction subrings

This leaf adds the scheme-facing maps and covering conclusions for a finite
family of subrings with a common fraction field.  The underlying
intersection and tensor maps remain in the RingTheory owner.
-/

@[expose] public section

open AlgebraicGeometry

universe u v

namespace FractionRing.SubringFamily

variable {K : Type u} [Field K]
variable {ι : Type v}

/-- The affine morphism from the spectrum of a component to the spectrum of the family
intersection. -/
noncomputable def specComponent (A : ι → Subring K) (i : ι) :
    Spec (CommRingCat.of (A i)) ⟶ Spec (CommRingCat.of (intersection A)) :=
  Spec.map (CommRingCat.ofHom (toComponent A i))

/-- The map on prime spectra induced by the inclusion from the family intersection into a
component. -/
def primeComponent (A : ι → Subring K) (i : ι) :
    PrimeSpectrum (A i) → PrimeSpectrum (intersection A) :=
  PrimeSpectrum.comap (toComponent A i)

/-- Compute the prime-spectrum component map as comap along the inclusion. -/
theorem primeComponent_apply (A : ι → Subring K) (i : ι) (x : PrimeSpectrum (A i)) :
    primeComponent A i x = PrimeSpectrum.comap (toComponent A i) x := sorry

/-- Under the pairwise-surjective tensor hypothesis, every component spectrum maps by an open
immersion into the spectrum of the family intersection. -/
@[stacks 09N4]
theorem specComponent_isOpenImmersion_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A)
    (i : ι) :
    IsOpenImmersion (specComponent A i) := sorry

/-- Under the pairwise-surjective tensor hypothesis, the open ranges of the component spectra
cover the spectrum of the family intersection. -/
@[stacks 09N4]
theorem specComponents_cover_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A) :
    (⨆ i : ι,
      @Scheme.Hom.opensRange _ _ (specComponent A i)
        (specComponent_isOpenImmersion_of_pairwiseTensorSurjective A hFraction hNoetherian
          hSemilocal hdim hSurj i)) = ⊤ := sorry

/-- Under the pairwise-surjective tensor hypothesis, every closed point of the family-intersection
spectrum belongs to the image of exactly one component spectrum. -/
@[stacks 09N4]
theorem existsUnique_component_of_closedPoint_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A)
    (x : PrimeSpectrum (intersection A))
    (hx : x ∈ closedPoints (PrimeSpectrum (intersection A))) :
    ∃! i : ι, x ∈ Set.range (primeComponent A i) := sorry

end FractionRing.SubringFamily
