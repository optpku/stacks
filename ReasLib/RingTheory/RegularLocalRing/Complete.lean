module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Complete Regular Local Rings

This leaf records permanence properties of complete regular local domains.
-/

universe u

namespace IsRegularLocalRing

/-- A complete regular local domain is an `N-2` ring. -/
theorem isN2Ring_of_completeLocal
    {R : Type u} [CommRing R] [IsDomain R] [IsCompleteLocalRing R]
    [IsRegularLocalRing R] : IsN2Ring R := sorry

end IsRegularLocalRing
