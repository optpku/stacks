/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Gorenstein.Ring

@[expose] public section

universe u

#check
  (IsGorensteinRing :
    (R : Type u) → [CommRing R] → Prop)

#check
  (IsGorensteinRing.instLocalizationAtPrime :
    (R : Type u) → [CommRing R] → [IsGorensteinRing R] →
      (p : Ideal R) → [p.IsPrime] →
        IsGorensteinLocalRing (Localization.AtPrime p))

#check
  (IsGorensteinRing.of_localizationAtPrime :
    (R : Type u) → [CommRing R] → [IsNoetherianRing R] →
      (∀ (p : Ideal R) [p.IsPrime], IsGorensteinLocalRing (Localization.AtPrime p)) →
        IsGorensteinRing R)

#check
  (isGorensteinRing_iff :
    (R : Type u) → [CommRing R] →
      IsGorensteinRing R ↔
        IsNoetherianRing R ∧
          ∀ (p : Ideal R) [p.IsPrime], IsGorensteinLocalRing (Localization.AtPrime p))
