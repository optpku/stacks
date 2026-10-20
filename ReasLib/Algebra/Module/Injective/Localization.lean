/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalProperties.Injective

@[expose] public section

universe u v

namespace Module.Injective

/-- Localization of an injective module over a Noetherian ring is injective over the
localized ring. -/
instance localizedModule (R : Type u) [CommRing R] [IsNoetherianRing R]
    (S : Submonoid R) (E : Type v) [Small.{v} R] [AddCommGroup E] [Module R E]
    [Module.Injective R E] : Module.Injective (Localization S) (LocalizedModule S E) := sorry

end Module.Injective
