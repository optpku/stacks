/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.RingTheory.LocalProperty
public import ReasLib.RingTheory.Normal.Localization

/-!
# Locality of normal rings

This file records that normality is invariant under ring isomorphisms and is
local for finite principal-open covers.
-/

@[expose] public section

universe u

namespace IsNormalRing

/-- Normality of commutative rings is invariant under isomorphisms. -/
@[instance]
theorem isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ _root_.IsNormalRing A) := sorry

/-- The normal-ring property is local for finite principal-open covers. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ _root_.IsNormalRing A) := sorry

end IsNormalRing
