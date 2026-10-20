module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral Y]

/-- Over a Noetherian integral target, a resolution of singularities is a modification with
regular source. -/
class IsResolution (f : X ⟶ Y) [IsNoetherian Y] [IsIntegral Y] : Prop
    extends IsModification f where
  /-- The source of a resolution of singularities is regular. -/
  regularSource : Scheme.Regular X

attribute [instance] IsResolution.regularSource

namespace IsResolution

/-- A modification with regular source is a resolution of singularities. -/
instance instOfProperties (f : X ⟶ Y) [IsModification f] [Scheme.Regular X] :
    IsResolution f := sorry

/-- A resolution of singularities is a modification and has regular source. -/
theorem spec (f : X ⟶ Y) [IsResolution f] :
    IsModification f ∧ Scheme.Regular X := sorry

end IsResolution

/-- Resolution of singularities is equivalent to modification together with regularity of the
source. -/
theorem isResolution_iff (f : X ⟶ Y) :
    IsResolution f ↔ IsModification f ∧ Scheme.Regular X := sorry

end AlgebraicGeometry
