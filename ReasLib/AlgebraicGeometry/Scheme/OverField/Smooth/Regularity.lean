module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A scheme smooth over a field is regular. -/
instance instRegularOfSmooth (X : SchemeOverField k) [Smooth X.hom] :
    Scheme.Regular X.left :=
  Scheme.Hom.regular_of_smooth_over_field X.hom

end AlgebraicGeometry.SchemeOverField

end
