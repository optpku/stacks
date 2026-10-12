/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Open Spectrum Images of Flat Maps

This leaf states the ring-hom form of the open-map theorem for a flat finitely
presented commutative algebra.
-/

universe u v

namespace PrimeSpectrum

/-- The image of `Spec S -> Spec R` is open when `R ->+* S` is flat and of
finite presentation. -/
@[stacks 034Z "open spectrum image of a flat finitely presented map"]
theorem isOpen_range_comap_of_flat_of_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (hflat : f.Flat) (hfp : f.FinitePresentation) :
    IsOpen (Set.range (PrimeSpectrum.comap f)) := sorry

end PrimeSpectrum
