/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flatness of adic completion

For any ideal of a Noetherian commutative ring, the canonical map from the ring
to its adic completion is flat.
@stack 0BNP
-/

universe u

/-- The canonical map from a Noetherian commutative ring to its completion
with respect to any ideal is flat. -/
@[stacks 00MB "compatibility",
  stacks 0BNP "Noetherian adic completion is flat"]
theorem adicCompletion_algebraMap_flat
    {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R] :
    (algebraMap R (AdicCompletion I R)).Flat := sorry
