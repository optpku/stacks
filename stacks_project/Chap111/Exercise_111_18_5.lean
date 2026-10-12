/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Catenary.TwistedFlags
import StacksCheckRecall

/-!
# Exercise 111.18.5

A finite sober catenary space with no integer dimension function, realized by
the twisted two-flag Alexandrov space `TwistedFlags.Point`. Its unit drops along
`eta ⤳ p` and `eta ⤳ a ⤳ q` force `δ p = δ q + 1`, while the two branches through
`xi` force `δ p = δ q`, so no dimension function can exist.
-/

@[expose] public section

open TopologicalSpace

/- Exercise 111.18.5 (1): the constructed space has no integer dimension function. -/
@[stacks 0CT6] #check
  (TwistedFlags.not_exists_isDimensionFunction :
    ¬ ∃ δ : TwistedFlags.Point → ℤ, IsDimensionFunction δ)

/- Exercise 111.18.5 (2): the constructed space is finite. -/
@[stacks 0CT6] #check (TwistedFlags.instFintypePoint : Fintype TwistedFlags.Point)

/- Exercise 111.18.5 (3): the constructed space is sober. -/
@[stacks 0CT6] #check
  (TwistedFlags.sober : T0Space TwistedFlags.Point ∧ QuasiSober TwistedFlags.Point)

/- Exercise 111.18.5 (4): the constructed space is catenary. -/
@[stacks 0CT6] #check
  (TwistedFlags.instCatenarySpace : TopologicalSpace.CatenarySpace TwistedFlags.Point)

/- The source definition is equivalent to the interpolating-gap formulation. -/
#check
  (TwistedFlags.isDimensionFunction_iff_interpolating :
    ∀ δ : TwistedFlags.Point → ℤ,
      IsDimensionFunction δ ↔
        (∀ ⦃x y : TwistedFlags.Point⦄, x ⤳ y → x ≠ y → δ y < δ x) ∧
          ∀ ⦃x y : TwistedFlags.Point⦄, x ⤳ y → δ y + 2 ≤ δ x →
            ∃ z : TwistedFlags.Point,
              x ⤳ z ∧ z ⤳ y ∧ δ z < δ x ∧ δ y < δ z)
