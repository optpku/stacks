module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications

/-!
# Local complete intersection morphisms from regular immersions

Regular immersions and Koszul-regular immersions of schemes are locally of type
`RingHom.IsLocalCompleteIntersection`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsKoszulRegularImmersion

/-- A Koszul-regular immersion of schemes is locally of type
`RingHom.IsLocalCompleteIntersection`. -/
@[instance]
theorem isLocalCompleteIntersection
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    LocallyOfType RingHom.IsLocalCompleteIntersection i := sorry

end IsKoszulRegularImmersion

namespace IsRegularImmersion

/-- A regular immersion of schemes is locally of type
`RingHom.IsLocalCompleteIntersection`. -/
theorem isLocalCompleteIntersection
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    LocallyOfType RingHom.IsLocalCompleteIntersection i := sorry

end IsRegularImmersion

end AlgebraicGeometry
