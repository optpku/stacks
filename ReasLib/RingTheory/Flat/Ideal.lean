module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat ideals

@stack 092S

This leaf records the filtered-colimit passage from finitely generated ideals to arbitrary
ideals.  It is independent of weak dimension and valuation theory.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- If every finitely generated ideal is flat, then every ideal is flat. -/
@[stacks 092S "flat ideals from finitely generated ideals"]
theorem flat_of_fg_flat
    (hfg : ∀ J : Ideal R, J.FG → Module.Flat R J) (I : Ideal R) :
    Module.Flat R I := sorry

end Ideal
