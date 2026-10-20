/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing

@[expose] public section

universe u v

/- The canonical tame symbol on the units of a total fraction ring. -/
#check (TameSymbol.Total.value :
  (A : Type u) → (K : Type v) → [CommRing A] → [IsLocalRing A] →
    [IsNoetherianRing A] → [CommRing K] → [Algebra A K] → [IsFractionRing A K] →
      ringKrullDim A = 1 → Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
