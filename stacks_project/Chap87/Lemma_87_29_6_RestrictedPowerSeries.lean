/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RestrictedPowerSeries.Quotient

@[expose] public section

universe u

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] [TopologicalSpace A]

#check (RingHom.IsClosedQuotientOfRestrictedPowerSeries : (B →+* A) → Prop)
