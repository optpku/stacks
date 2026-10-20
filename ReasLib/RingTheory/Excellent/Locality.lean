/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.RingTheory.LocalProperty
public import ReasLib.RingTheory.Excellent

/-!
# Locality of (quasi-)excellent rings

Quasi-excellence and excellence of commutative rings are invariant under ring
isomorphisms and local for finite principal-open covers.
-/

@[expose] public section

universe u

namespace IsQuasiExcellentRing

/-- The quasi-excellent property of commutative rings is invariant under
isomorphisms. -/
instance isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u,u} A) := sorry

/-- The quasi-excellent property is local for finite principal-open covers. -/
instance ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u,u} A) :=
  sorry

end IsQuasiExcellentRing

namespace IsExcellentRing

/-- The excellent property of commutative rings is invariant under
isomorphisms. -/
instance isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u,u} A) := sorry

/-- The excellent property is local for finite principal-open covers. -/
instance ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u,u} A) :=
  sorry

end IsExcellentRing
