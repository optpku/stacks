module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Characterization

@[expose] public section

/-!
# Smooth Descent of Nagata Rings

This leaf separates the intrinsic faithfully-flat descent statement from the
usual smooth map formulation obtained by assuming surjectivity on prime
spectra.
-/

universe u v

namespace NagataRing

/-- A Nagata target descends the Nagata property along a smooth faithfully flat
algebra map. -/
@[stacks 0354 "faithfully flat formulation"]
theorem of_smooth_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (h : (algebraMap R S).FaithfullyFlat) [NagataRing S] :
    NagataRing R := sorry

/-- If `R → S` is smooth and surjective on prime spectra, then a Nagata target
`S` makes `R` Nagata. -/
@[stacks 0354]
theorem of_smooth_of_specComap_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) [NagataRing S] :
    NagataRing R := sorry

end NagataRing
