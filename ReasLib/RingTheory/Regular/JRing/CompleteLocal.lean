module

public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete Local J-2 Rings

@stack 07PI
@stack 07PJ

The `J-2` structure on a Noetherian complete local ring is canonical, so it is exposed as a
named global instance.
-/

universe u v

namespace IsJ0Ring

/-- Every Noetherian complete local domain is `J-0`. -/
@[stacks 07PI "complete local domains are J-0"]
instance completeLocalDomain (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] [IsDomain R] : IsJ0Ring R := sorry

end IsJ0Ring

namespace IsJ2Ring

/-- Every Noetherian complete local ring is `J-2`. -/
@[stacks 07PJ "(2), complete local rings"]
instance completeLocal (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] : IsJ2Ring.{u, v} R := sorry

end IsJ2Ring
