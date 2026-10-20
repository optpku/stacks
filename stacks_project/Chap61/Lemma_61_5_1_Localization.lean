/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Specializing

@[expose] public section

universe u

/- A typed compatibility check for the specializing localization API. -/
#check (Localization.specializing :
  ∀ {A : Type u} [CommRing A], A → Ideal A → Type u)
