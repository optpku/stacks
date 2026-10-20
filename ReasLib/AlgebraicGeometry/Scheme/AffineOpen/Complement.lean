module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affineness from complementary affine opens
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme covered by two complementary affine opens is affine. -/
@[stacks 01I5]
theorem isAffine_of_isCompl_of_isAffineOpen
    {X : Scheme.{u}} {U V : X.Opens}
    (hcompl : IsCompl U V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
