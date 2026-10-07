module

public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation

/-!
# Separating closed subsets of prime spectra

This leaf converts disjointness of a closed subset from the closure of a
spectrum image into an ideal equation and an element-level separator.

@stack 07M3
-/

@[expose] public section

open Topology PrimeSpectrum
open scoped PrimeSpectrum

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Disjointness of `closure (comap φ '' V(J))` from `V(I)` forces the sum of `I` and the
contraction of `J` to be the unit ideal. -/
theorem sup_comap_eq_top_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    I ⊔ J.comap φ = ⊤ := sorry

/-- Lemma 15.9.8 (07M3): if the closure of the image of `V(J)` in `Spec(R)` is disjoint
from `V(I)`, there is an element of `R` equal to `1` modulo `I` whose image in `S` lies in
`J`. -/
@[stacks 07M3 "an element separating closed subsets"]
theorem exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    ∃ r : R, Ideal.Quotient.mk I r = 1 ∧ φ r ∈ J := sorry
