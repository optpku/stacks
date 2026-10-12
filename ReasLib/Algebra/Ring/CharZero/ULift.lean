/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Ring.ULift

@[expose] public section

universe u v

namespace ULift

/-- A universe lift of an additive monoid with one of characteristic zero has
characteristic zero. -/
instance instCharZero {R : Type u} [AddMonoidWithOne R] [CharZero R] :
    CharZero (ULift.{v} R) where
  cast_injective := fun _ _ equality ↦ Nat.cast_injective (congrArg ULift.down equality)

end ULift
