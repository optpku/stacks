/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.DimensionTwo
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.18.3: a Noetherian local domain of dimension two is catenary. -/
@[stacks 02DS] #check (IsCatenaryRing.of_isDomain_isLocalRing_ringKrullDim_eq_two :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R],
    ringKrullDim R = 2 → IsCatenaryRing R)
