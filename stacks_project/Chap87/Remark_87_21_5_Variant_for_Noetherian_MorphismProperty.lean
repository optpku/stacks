/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Local properties of morphisms of Noetherian adic rings

Typed compatibility checks for Noetherian ring locality and its foundations.
-/

@[expose] public section

universe u

open TopologicalRing

#check (TopologicalRing.Noetherian.IsLocalMorphismProperty :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)

#check (TopologicalRing.Noetherian.instIsCountablyIndexed :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsAdicRing A] [IsNoetherianRing A], IsCountablyIndexed A)

#check (TopologicalRing.instIsAdicRingPi :
  ∀ {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsAdicRing (A i)], IsAdicRing (∀ i, A i))

#check (TopologicalRing.weakIdealCompletion.instIsAdicRing :
  ∀ {A A' : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing A'] [Algebra A A'] [IsNoetherianRing A'],
    IsAdicRing (weakIdealCompletion A A'))
