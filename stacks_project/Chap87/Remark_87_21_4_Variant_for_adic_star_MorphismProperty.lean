/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.AdicStar.LocalMorphismProperty

/-! # Local properties of adic-star ring homomorphisms -/

@[expose] public section

open TopologicalRing

universe u

#check (TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty :
  (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop) → Prop)
