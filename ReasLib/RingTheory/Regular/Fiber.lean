module

public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fibers of regular ring maps

This module collects intrinsic ring-theoretic consequences of the fiber clause
in `RingHom.Regular`.

@stack 07BZ
-/

namespace RingHom.Regular

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}

/-- Every fiber of a regular ring map is Noetherian. -/
@[stacks 07BZ "Noetherian regular fibers"]
theorem isNoetherianRing_fiber (h : f.Regular) (p : PrimeSpectrum R) :
    IsNoetherianRing (f.Fiber p.asIdeal) := sorry

/-- Every fiber of a regular ring map is reduced. -/
@[stacks 07BZ "reduced regular fibers"]
theorem isReduced_fiber (h : f.Regular) (p : PrimeSpectrum R) :
    IsReduced (f.Fiber p.asIdeal) := sorry

end RingHom.Regular
