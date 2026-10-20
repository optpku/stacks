/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Catenary.Basic

@[expose] public section

universe u

namespace IsCatenaryRing

/-- A Noetherian local domain of Krull dimension two is catenary. -/
@[stacks 02DS]
theorem of_isDomain_isLocalRing_ringKrullDim_eq_two {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] (hdim : ringKrullDim R = 2) :
    IsCatenaryRing R := sorry

/-- A Noetherian local domain with Krull dimension two supplied as a fact is catenary. -/
instance instOfIsDomainIsLocalRingRingKrullDimEqTwo {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] [Fact (ringKrullDim R = 2)] :
    IsCatenaryRing R :=
  of_isDomain_isLocalRing_ringKrullDim_eq_two Fact.out

end IsCatenaryRing
