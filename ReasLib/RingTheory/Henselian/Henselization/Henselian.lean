module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Finite
public import ReasLib.RingTheory.Henselian.Henselization

@[expose] public section

/-!
# Henselizations over Henselian Bases

This leaf records the reusable rigidity of a henselization when its base is
already henselian.  It intentionally exposes only proposition-valued
consequences, rather than choosing an inverse to the structural map.
-/

universe u v

namespace IsHenselizationOf

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- The structural map from a henselian local ring to any chosen henselization
is bijective. -/
theorem algebraMap_bijective_of_henselian :
    Function.Bijective (algebraMap R S) := sorry

/-- A henselization over a henselian local base is finite over that base.  This
is the direct finite-map consequence of
`algebraMap_bijective_of_henselian`. -/
theorem algebraMap_finite_of_henselian :
    (algebraMap R S).Finite := sorry

end IsHenselizationOf
