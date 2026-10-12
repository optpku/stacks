/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Normal Noetherian Domains and N-1

This leaf records the basic bridge from normality to the `N-1` condition.
-/

universe u

namespace IsNormalRing

/-- A Noetherian normal domain is `N-1`. -/
theorem isN1Ring {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsNormalRing R] : IsN1Ring R := sorry

end IsNormalRing
