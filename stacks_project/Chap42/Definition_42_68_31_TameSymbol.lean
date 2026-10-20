/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant

@[expose] public section

universe u v

/- Compatibility check for the determinant construction of the tame symbol. -/
#check
  (TameSymbol.value :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K],
      ringKrullDim A = 1 →
        Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
