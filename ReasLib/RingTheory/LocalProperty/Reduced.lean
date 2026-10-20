module

public import ReasLib.RingTheory.LocalProperty
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Locality of Reduced Rings

This leaf packages the principal-open locality instance for mathlib's
`IsReduced` predicate.
-/

@[expose] public section

universe u

namespace IsReduced

/-- The reduced-ring property is local for finite principal-open covers. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ _root_.IsReduced A) := sorry

end IsReduced
