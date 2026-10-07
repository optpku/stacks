module

public import ReasLib.RingTheory.DividedPowers.Category
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Colimits of Divided Power Rings

This module owns the global colimit instance for the category of divided power rings.
-/

open CategoryTheory.Limits

universe u

namespace DividedPowerRing

/-- The category of divided power rings has all small colimits. -/
@[stacks 07GX]
instance hasColimits : HasColimits DividedPowerRing.{u} := sorry

end DividedPowerRing
