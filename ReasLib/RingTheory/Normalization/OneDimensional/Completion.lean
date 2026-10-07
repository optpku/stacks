module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normalization.OneDimensional

/-!
# Completions of one-dimensional normalizations

This leaf records the local, reduced, Nagata, and dimension-one properties of
the maximal-ideal completion of a reduced Nagata local ring.
-/

@[expose] public section

open IsLocalRing

universe u

namespace Normalization.OneDimensional.Completion

variable {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]

/-- The maximal-ideal completion of a reduced one-dimensional Nagata local ring is local. -/
@[stacks 0C3V]
theorem isLocalRing (h_dimension : ringKrullDim A = 1) :
    IsLocalRing (AdicCompletion (maximalIdeal A) A) := sorry

/-- The maximal-ideal completion of a reduced one-dimensional Nagata local ring is reduced. -/
@[stacks 0C3V]
theorem isReduced (h_dimension : ringKrullDim A = 1) :
    IsReduced (AdicCompletion (maximalIdeal A) A) := sorry

/-- The maximal-ideal completion of a reduced one-dimensional Nagata local ring is Nagata. -/
@[stacks 0C3V]
theorem isNagataRing (h_dimension : ringKrullDim A = 1) :
    NagataRing (AdicCompletion (maximalIdeal A) A) := sorry

/-- The maximal-ideal completion of a reduced one-dimensional Nagata local ring has Krull
dimension one. -/
@[stacks 0C3V]
theorem krullDim_eq_one (h_dimension : ringKrullDim A = 1) :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1 := sorry

end Normalization.OneDimensional.Completion
