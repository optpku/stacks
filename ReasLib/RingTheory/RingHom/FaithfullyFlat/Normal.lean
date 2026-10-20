/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normality Descent Along Faithfully Flat Maps

The result is stated for a ring homomorphism rather than a chosen algebra
structure, so it is available to all faithfully flat descent arguments.
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Normality descends along a faithfully flat ring homomorphism. -/
@[stacks 033G, stacks 0FIZ "normality descends along faithfully flat maps"]
theorem isNormalRing {f : R →+* S} (hff : f.FaithfullyFlat) [IsNormalRing S] :
    IsNormalRing R := sorry

end RingHom.FaithfullyFlat
