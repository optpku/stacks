/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.VanishingStratum
import StacksCheckRecall

@[expose] public section

universe u

open PrimeSpectrum

/- 61.5.1.1: for a ring `A` and a disjoint decomposition of a finite subset
`E = E' ⨿ E''` of `A`, the vanishing-pattern stratum `Z(E', E'') ⊆ Spec(A)` is
`vanishingStratum E' E''`, and the two presentations coincide:
`⋂ f ∈ E', D(f) ∩ ⋂ f ∈ E'', V(f) = D(∏ f ∈ E', f) ∩ V(span E'')`. -/
@[stacks 096W] #check (PrimeSpectrum.stratum_eq :
  ∀ {A : Type u} [CommRing A] (E' E'' : Finset A),
    (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)) =
      (basicOpen (∏ f ∈ E', f) : Set (PrimeSpectrum A)) ∩
        zeroLocus ((Ideal.span (E'' : Set A) : Set A)))

#check (PrimeSpectrum.vanishingStratum_eq_iInter :
  ∀ {A : Type u} [CommRing A] (E' E'' : Set A),
    PrimeSpectrum.vanishingStratum E' E'' =
      (⋂ f ∈ E', (basicOpen f : Set (PrimeSpectrum A))) ∩
        (⋂ f ∈ E'', zeroLocus ({f} : Set A)))
