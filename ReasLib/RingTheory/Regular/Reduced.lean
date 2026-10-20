/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.Fiber
public import ReasLib.RingTheory.RingHom.Fiber.Reduced
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reducedness along regular ring maps

@stack 07QK

This leaf composes the reusable fiberwise reducedness theorem for regular maps
with flat ascent of reducedness.
-/

@[expose] public section

universe u v

namespace RingHom.Regular

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsReduced R]

/-- A regular map between Noetherian rings carries reducedness from its source to its target. -/
@[stacks 07QK "reducedness along a regular ring map"]
theorem isReduced {f : R →+* S} (h : f.Regular) : IsReduced S := sorry

end RingHom.Regular
