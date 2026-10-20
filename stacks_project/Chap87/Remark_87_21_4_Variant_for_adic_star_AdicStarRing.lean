/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.AdicStar

/-! # Adic-star rings -/

@[expose] public section

universe u

#check (TopologicalRing.IsAdicStarRing :
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R], Prop)
