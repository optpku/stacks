module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (r : ℕ)

/- Fixed relative dimension is stable under arbitrary pullback squares of schemes. -/
#check (AlgebraicGeometry.Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange
    r :
    MorphismProperty.IsStableUnderBaseChange
      (fun (_ _ : Scheme.{u}) f ↦ RelativeDimension f r))

end AlgebraicGeometry.Scheme.Hom
