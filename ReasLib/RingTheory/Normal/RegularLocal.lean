module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Normal.Ring
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normality of regular local rings

This leaf owns the local specialization of regularity implying normality.  The
global statement for `IsRegularRing` remains in `Normal.Regular`; keeping the
local theorem separate preserves the distinction between the two predicates.
-/

universe u

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-- Every regular local ring is normal. -/
@[stacks 0567 "regular local rings are normal"]
theorem isNormalRing [IsRegularLocalRing R] : IsNormalRing R := sorry

end IsRegularLocalRing

end
