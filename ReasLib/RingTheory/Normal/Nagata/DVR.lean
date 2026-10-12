/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Quotient

@[expose] public section

/-!
# Nagata Discrete Valuation Rings

@stack 09E1

This leaf records the DVR-specific direction relating the `N-2` and Nagata
conditions.  The converse is the general domain theorem
`NagataRing.isN2Ring`.
-/

universe u

namespace IsN2Ring

/-- Example 10.162.17 (1), tag `09E1`: an `N-2` discrete valuation ring is
Nagata. -/
@[stacks 09E1 "N-2 DVRs are Nagata"]
theorem nagataRing_of_discreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsN2Ring R] :
    NagataRing R := sorry

end IsN2Ring

namespace NagataRing

/-- Example 10.162.17 (1), tag `09E1`: a discrete valuation ring is Nagata
exactly when it is `N-2`. -/
@[stacks 09E1]
theorem iff_isN2Ring_of_discreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    NagataRing R ↔ IsN2Ring R := sorry

end NagataRing
