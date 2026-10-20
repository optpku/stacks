/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Nagata Properties of Complete Local Rings

This leaf records the reusable `N-2` and Nagata consequences of complete-local
structure.
-/

universe u

namespace IsCompleteLocalRing

/-- A Noetherian complete local domain is an `N-2` ring. -/
theorem isN2Ring_of_domain
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] : IsN2Ring R := sorry

/-- A Noetherian complete local ring is Nagata. -/
@[stacks 032W]
instance nagataRing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] : NagataRing R := sorry

end IsCompleteLocalRing
