module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Locus.Away

/-!
# Local density criteria for the generic-flatness locus

This leaf contains the topological local-to-global step independently of the
algebraic arguments that supply density on each principal open.

@stack 051Y
-/

@[expose] public section

universe u v w x

namespace GenericFlatness

/-- The generic-flatness good locus is dense if it is dense on every member of a dense union of
principal opens. -/
@[stacks 051Y "local density criterion for the generic-flatness locus"]
theorem dense_of_dense_basicOpen_cover
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    {ι : Type x} (f : ι → R)
    (hcover : Dense (⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R))))
    (hdense :
      ∀ i, Dense (((↑) : PrimeSpectrum.basicOpen (f i) → PrimeSpectrum R) ⁻¹'
        goodLocus R S M)) :
    Dense (goodLocus R S M) := sorry

/-- Lemma 10.118.6: if a dense open subset of `Spec(R)` is covered by basic
opens and the localized generic-flatness good locus is dense over every member
of the cover, then the original good locus is dense. -/
@[stacks 051Y "density from localized generic-flatness loci"]
theorem dense_of_localized_cover
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M]
    {U : Set (PrimeSpectrum R)} (hUopen : IsOpen U) (hUdense : Dense U)
    {ι : Type x} (f : ι → R)
    (hcover : U = ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum R)))
    (hdense : ∀ i, Dense (goodLocusAway (R := R) (S := S) (M := M) (f i))) :
    Dense (goodLocus R S M) := sorry

end GenericFlatness
