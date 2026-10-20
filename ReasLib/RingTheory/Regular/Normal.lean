/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Normal
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normality along Regular Ring Maps

@stack 0BFK
-/

@[expose] public section

universe u v

namespace RingHom.Regular

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 15.42.2 (0BFK): a regular ring map with Noetherian normal source and Noetherian
target has normal target. -/
@[stacks 0BFK "normality along a regular ring map"]
theorem isNormalRing {f : R →+* S} (h : f.Regular)
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNormalRing R] :
    IsNormalRing S := sorry

end RingHom.Regular
