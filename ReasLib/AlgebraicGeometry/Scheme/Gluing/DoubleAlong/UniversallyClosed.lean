module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.DoubleAlong

/-- The fold from two copies of a scheme glued along an open subscheme is universally closed. -/
instance instUniversallyClosed_fold {X : Scheme.{u}} (U : X.Opens) :
    UniversallyClosed (fold U) := by
  sorry

end AlgebraicGeometry.Scheme.DoubleAlong
