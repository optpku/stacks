module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

/-!
# Cohen--Macaulayness of Regular Rings

@stack 00NQ

This leaf records the two canonical directions from regularity to
Cohen--Macaulayness.  The local statement concerns the self-module of a
regular local ring; the global statement packages its primewise consequence
for a regular ring.
-/

universe u

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R]

/-- The self-module of a regular local ring is Cohen--Macaulay. -/
@[stacks 00NQ "regular local ring self-module is Cohen-Macaulay"]
theorem self_of_isRegularLocalRing [IsRegularLocalRing R] :
    Module.CohenMacaulay R R := sorry

/-- A regular local ring supplies the canonical Cohen--Macaulay structure on
its self-module. -/
@[stacks 00NQ "regular local ring self-module is Cohen-Macaulay"]
instance instSelfOfIsRegularLocalRing [IsRegularLocalRing R] :
    Module.CohenMacaulay R R := sorry

end Module.CohenMacaulay

namespace CohenMacaulayRing

variable {R : Type u} [CommRing R]

/-- A regular ring is Cohen--Macaulay, obtained by applying the regular-local
self-module statement at every prime. -/
@[stacks 00NQ "regular rings are Cohen-Macaulay"]
theorem of_isRegularRing (hR : IsRegularRing R) : CohenMacaulayRing R := sorry

/-- Regularity supplies the canonical Cohen--Macaulay ring structure in the
forward direction. -/
@[stacks 00NQ "regular rings are Cohen-Macaulay"]
instance instOfIsRegularRing [IsRegularRing R] : CohenMacaulayRing R := sorry

end CohenMacaulayRing
