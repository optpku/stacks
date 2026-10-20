module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DividedPowers.Category.Pushout

@[expose] public section

/-!
# The Forgetful Functor from Divided Power Rings

The forgetful functor to commutative rings creates limits but does not preserve pushouts, hence
does not preserve all colimits.
-/

open CategoryTheory CategoryTheory.Limits

namespace DividedPowerRing

namespace forgetCommRing

/-- The forgetful functor from divided power rings to commutative rings does not preserve all
pushouts. -/
theorem notPreservesPushouts :
    ¬ PreservesColimitsOfShape WalkingSpan DividedPowerRing.forgetCommRing := sorry

/-- Remark 23.3.6 (Tag 07GY): the forgetful functor from divided power rings to commutative rings
does not preserve all colimits. -/
@[stacks 07GY]
theorem notPreservesColimits : ¬ PreservesColimits DividedPowerRing.forgetCommRing := sorry

end forgetCommRing

end DividedPowerRing
