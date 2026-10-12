/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.LocalProperty

/-!
# Locality of Regular Rings

This leaf packages the principal-open locality instance for mathlib's
`IsRegularRing` predicate.
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Regularity of commutative rings is invariant under ring isomorphisms. -/
@[instance]
theorem isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ IsRegularRing A) := sorry

/-- The regular-ring property is local for finite principal-open covers. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ IsRegularRing A) := sorry

end IsRegularRing
