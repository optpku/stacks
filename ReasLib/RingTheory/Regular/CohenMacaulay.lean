module

public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.Flat.Fiber.Serre
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohen-Macaulayness along Regular Ring Maps

@stack 0H7T
-/

@[expose] public section

universe u v

namespace RingHom.Regular

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 15.42.4 (0H7T): a regular ring map with Cohen-Macaulay source and Noetherian target
has Cohen-Macaulay target. -/
@[stacks 0H7T "Cohen-Macaulayness along a regular ring map"]
theorem cohenMacaulayRing {f : R →+* S} (h : f.Regular)
    [CohenMacaulayRing R] [IsNoetherianRing S] :
    CohenMacaulayRing S := sorry

end RingHom.Regular
