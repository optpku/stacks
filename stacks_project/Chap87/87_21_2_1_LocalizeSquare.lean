/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.LocalizeSquare

@[expose] public section

universe u

/- A countably indexed topological ring has a countable open-ideal basis at zero. -/
#check (TopologicalRing.IsCountablyIndexed :
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R], Prop)

/- The localization square records continuous vertical maps between étale weak-ideal
completions that commute with the canonical horizontal maps. -/
#check (TopologicalRing.LocalizeSquare :
  ∀ (A B A' B' : Type u)
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsCountablyIndexed B]
    [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    [CommRing B'] [Algebra B B'] [Algebra.Etale B B'], Type u)
