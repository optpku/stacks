module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Fiber

@[expose] public section

/-!
# Local Krull dimension for quasi-finite maps

The owner is `Algebra.QuasiFiniteAt`: quasi-finiteness at a target prime first
controls prime height, and for finite-type maps it consequently controls the
Krull dimension of the corresponding local ring.

@stack 00QF
@stack 00PL
-/

universe u v

namespace Algebra.QuasiFiniteAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- At a quasi-finite point, the height of a target prime is at most the height of its
contraction. -/
@[stacks 00QF "quasi-finite prime height comparison"]
theorem height_le_under_height
    (q : PrimeSpectrum S) [Algebra.QuasiFiniteAt R q.asIdeal] :
    q.asIdeal.height ≤ (q.asIdeal.under R).height := sorry

/-- For a finite-type map that is quasi-finite at a target prime, the target local ring has
Krull dimension at most that of the local ring at the contracted prime. -/
@[stacks 00QF "quasi-finite local Krull-dimension comparison"]
theorem ringKrullDim_localizationAtPrime_le
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime (q.under R)) := sorry

end Algebra.QuasiFiniteAt

namespace Algebra.QuasiFinite

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A quasi-finite map has zero-dimensional local fibers.  This is stated at the selected
target prime, so consumers do not have to choose a presentation of the fiber or a localization
of it. -/
@[stacks 00PL "quasi-finite local fibers"]
theorem ringKrullDim_fiberLocalRingAt_eq_zero
    [Algebra.QuasiFinite R S] (q : PrimeSpectrum S) :
    ringKrullDim (fiberLocalRingAt R S q) = 0 := sorry

end Algebra.QuasiFinite
