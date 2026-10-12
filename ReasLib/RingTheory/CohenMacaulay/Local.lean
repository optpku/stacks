/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.LocalProperty

/-!
# Locality of Cohen-Macaulay Rings

This file records that the Cohen-Macaulay property is invariant under ring
isomorphisms and local for finite principal-open covers.
-/

@[expose] public section

universe u

namespace CohenMacaulayRing

/-- The Cohen-Macaulay property of commutative rings is invariant under isomorphisms. -/
@[instance]
theorem isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) := sorry

/-- The Cohen-Macaulay property is local for finite principal-open covers. -/
@[stacks 01OT, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) := sorry

end CohenMacaulayRing
