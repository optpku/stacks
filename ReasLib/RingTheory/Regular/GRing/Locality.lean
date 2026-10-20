/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.RingTheory.LocalProperty
public import ReasLib.RingTheory.Regular.GRing

/-!
# Locality of G-rings

The G-ring property is invariant under ring isomorphisms and local for finite
principal-open covers.
-/

@[expose] public section

universe u

namespace IsGRing

/-- The G-ring property of commutative rings is invariant under isomorphisms. -/
instance isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ IsGRing A) := sorry

/-- The G-ring property is local for finite principal-open covers. -/
instance ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ IsGRing A) := sorry

end IsGRing
