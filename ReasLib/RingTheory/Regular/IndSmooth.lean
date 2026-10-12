/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndSmooth.Basic
public import ReasLib.RingTheory.Regular.RingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Noetherian fibers of ind-smooth maps

@stack 07EP
-/

namespace RingHom.IndSmooth

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {f : R →+* S}

/-- Lemma 15.41.5: an ind-smooth map with Noetherian fibers is regular. -/
@[stacks 07EP "ind-smooth maps with Noetherian fibers are regular"]
theorem regular_of_noetherianFibers (h : f.IndSmooth)
    (hfiber : ∀ p : PrimeSpectrum R, IsNoetherianRing (f.Fiber p.asIdeal)) :
    f.Regular := sorry

end RingHom.IndSmooth
