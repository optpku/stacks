module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# One-dimensional local domains

@stack 02MH

This leaf names the elementary specialization of the Krull-dimension bound that is repeatedly
used for lattices and discrete valuation arguments.  The upper bound is an instance, while the
non-field hypothesis supplies the strict lower bound.
-/

@[expose] public section

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
variable [Ring.KrullDimLE 1 R]

/-- A non-field local domain of Krull dimension at most one has dimension exactly one. -/
@[stacks 02MH "one-dimensional local-domain specialization"]
theorem ringKrullDim_eq_one_of_not_isField (hR : ¬ IsField R) :
    ringKrullDim R = 1 := sorry

end IsLocalRing
