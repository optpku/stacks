module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universe Lifts of Regular Local Rings

This leaf provides the canonical regular-local-ring instance on a universe
lift.  It is intrinsic transport across the `ULift` ring equivalence.

@stack 0523
-/

universe u v

namespace ULift

/-- A universe lift of a regular local ring is canonically regular local. -/
@[stacks 0523 "regular local rings under universe lift"]
instance instIsRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (ULift.{v} R) := sorry

/-- Regular-local-ring structure is invariant under the canonical universe lift. -/
@[stacks 0523 "regular local rings invariant under universe lift"]
theorem isRegularLocalRing_iff {R : Type u} [CommRing R] :
    IsRegularLocalRing (ULift.{v} R) ↔ IsRegularLocalRing R := sorry

end ULift
