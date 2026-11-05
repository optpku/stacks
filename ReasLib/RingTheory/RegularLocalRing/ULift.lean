/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

/-!
# Universe Lifts of Regular Local Rings

This leaf provides the canonical regular-local-ring instance on a universe
lift.  It is intrinsic transport across the `ULift` ring equivalence.
-/

universe u v

namespace ULift

/-- A universe lift of a regular local ring is canonically regular local. -/
instance instIsRegularLocalRing {R : Type u} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (ULift.{v} R) :=
  IsRegularLocalRing.of_ringEquiv ULift.ringEquiv.symm

/-- Regular-local-ring structure is invariant under the canonical universe lift. -/
theorem isRegularLocalRing_iff {R : Type u} [CommRing R] :
    IsRegularLocalRing (ULift.{v} R) ↔ IsRegularLocalRing R := by
  constructor
  · intro h
    letI := h
    exact IsRegularLocalRing.of_ringEquiv ULift.ringEquiv
  · intro h
    letI := h
    infer_instance

end ULift
