module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normal.Ring
public import ReasLib.RingTheory.Normalization.Basic

@[expose] public section

/-!
# One-Dimensional Local Normalizations

This module contains normalization facts whose natural hypotheses are a reduced Nagata
one-dimensional local ring.
-/

universe u

open scoped nonZeroDivisors

namespace Normalization

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R]

/-- The normalization of a reduced Nagata one-dimensional local ring is normal. -/
@[stacks 0C3S]
theorem isNormalRing_of_reduced_nagataRing_local_dimOne
    (hdim : ringKrullDim R = 1) :
    IsNormalRing (normalizationRing R) := sorry

/-- The normalization of a reduced Nagata one-dimensional local ring is a Nagata ring. -/
theorem isNagataRing_of_reduced_nagataRing_local_dimOne
    (hdim : ringKrullDim R = 1) :
    NagataRing (normalizationRing R) := sorry

/-- The normalization of a reduced Nagata one-dimensional local ring is module-finite over
the original ring. -/
theorem moduleFinite_of_reduced_nagataRing_local_dimOne
    (hdim : ringKrullDim R = 1) :
    Module.Finite R (normalizationRing R) := sorry

/-- The normalization quotient of a reduced Nagata one-dimensional local ring has finite
length as a module over the original ring. -/
theorem quotient_isFiniteLength_of_reduced_nagataRing_local_dimOne
    (hdim : ringKrullDim R = 1) :
    IsFiniteLength R (quotient R) := sorry

/-- The normalization `δ`-invariant of a reduced Nagata one-dimensional local ring vanishes
exactly when the ring is a domain and a discrete valuation ring. -/
@[stacks 0C3U]
theorem deltaInvariant_eq_zero_iff_isDiscreteValuationRing
    (hdim : ringKrullDim R = 1) :
    deltaInvariant R = 0 ↔ ∃ (_ : IsDomain R), IsDiscreteValuationRing R := sorry

end

end Normalization
