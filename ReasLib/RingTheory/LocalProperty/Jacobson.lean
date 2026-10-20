/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalProperty
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Locality of Jacobson Rings

This file supplies the principal-open locality instance for Jacobson commutative rings.
-/

@[expose] public section

universe u

namespace IsJacobsonRing

/-- The Jacobson-ring property is local for finite principal-open covers. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ _root_.IsJacobsonRing A) := sorry

end IsJacobsonRing
