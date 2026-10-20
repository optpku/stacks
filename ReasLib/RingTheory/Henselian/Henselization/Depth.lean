module

public import ReasLib.RingTheory.Flat.Fiber.Depth
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.Noetherian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Depth and henselization

Henselization and strict henselization preserve the depth of a Noetherian
local ring.

@stack 06LL
-/

@[expose] public section

universe u v

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.8 (1) (06LL): a Noetherian local ring and a
henselization have the same depth. -/
@[stacks 06LL "depth of a Henselization"]
theorem moduleDepth_eq : moduleDepth R R = moduleDepth S S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- Lemma 15.45.8 (2) (06LL): a Noetherian local ring and a strict
henselization have the same depth. -/
@[stacks 06LL "depth of a strict Henselization"]
theorem moduleDepth_eq : moduleDepth R R = moduleDepth S S := sorry

end IsStrictHenselizationOf
