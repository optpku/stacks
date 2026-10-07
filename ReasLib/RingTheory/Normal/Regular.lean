module

public import ReasLib.RingTheory.CohenMacaulay.Regular
public import ReasLib.RingTheory.Normal.Serre
public import ReasLib.RingTheory.RegularLocalRing.SerreCondition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normality of regular rings

Regularity supplies Serre's condition `(R₁)`, while the Cohen--Macaulay
property of regular rings supplies `(S₂)`.  Serre's criterion therefore gives
normality.

@stack 0567
-/

universe u

namespace IsRegularRing

variable {R : Type u} [CommRing R]

/-- A regular commutative ring is normal. -/
@[stacks 0567 "regular rings are normal"]
theorem isNormalRing [IsRegularRing R] : IsNormalRing R := by
  exact IsNormalRing.of_serre
    (IsRegularRing.serreConditionR 1)
    (CohenMacaulayRing.serreS R 2)

end IsRegularRing
