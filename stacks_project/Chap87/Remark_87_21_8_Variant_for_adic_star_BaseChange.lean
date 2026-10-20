/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.AdicStar.BaseChange

/-! # Stability of adic-star morphism properties under completed base change -/

@[expose] public section

open TopologicalRing

universe u

#check (TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop) → Prop)
