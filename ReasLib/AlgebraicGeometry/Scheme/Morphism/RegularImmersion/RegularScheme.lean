module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Regular immersions between regular schemes

An immersion whose source and target are regular schemes is a regular immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An immersion between regular schemes is a regular immersion. -/
@[instance]
theorem isRegularImmersion_of_isImmersion_of_regular
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [Scheme.Regular Z] [Scheme.Regular X] :
    IsRegularImmersion i := sorry

end AlgebraicGeometry
