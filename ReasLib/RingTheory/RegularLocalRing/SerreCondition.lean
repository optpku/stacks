/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Regular rings and Serre's conditions

Regularity of all prime localizations implies every finite Serre regularity
condition.  This leaf keeps that bridge with the regular-ring owner.

@stack 00OD
-/

universe u

namespace IsRegularRing

variable {R : Type u} [CommRing R]

/-- A regular ring satisfies Serre's condition `(R_k)` for every `k`. -/
@[stacks 00OD "regular rings satisfy Serre's condition (R_k)"]
theorem serreConditionR (k : ℕ) [IsRegularRing R] : SerreConditionR R k := sorry

end IsRegularRing
