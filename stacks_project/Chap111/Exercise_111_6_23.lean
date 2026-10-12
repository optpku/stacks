/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.RingTheory.Spectrum.Prime.ClosedPoint
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.23: closed points of `Spec(A)` correspond to maximal ideals of `A`.
A point `x` of `PrimeSpectrum A` belongs to `closedPoints (PrimeSpectrum A)` if and only
if `x.asIdeal.IsMaximal`. -/
@[stacks 02DD]
#check (PrimeSpectrum.mem_closedPoints_iff_isMaximal :
  ∀ {R : Type u} [CommRing R] (x : PrimeSpectrum R),
    x ∈ closedPoints (PrimeSpectrum R) ↔ x.asIdeal.IsMaximal)

/- Companion: `x ∈ closedPoints X` iff `IsClosed {x}`. -/
#check @mem_closedPoints_iff

/- Companion: the range of `MaximalSpectrum.toPrimeSpectrum` is `{x | IsClosed {x}}`. -/
#check @MaximalSpectrum.toPrimeSpectrum_range

/- Companion: the inclusion `MaximalSpectrum R → PrimeSpectrum R` is injective. -/
#check @MaximalSpectrum.toPrimeSpectrum_injective
