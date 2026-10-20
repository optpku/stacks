module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Implications
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Implications between regularity conditions for immersions

Regular immersions are Koszul-regular, Koszul-regular immersions are
`H₁`-regular, and `H₁`-regular immersions are quasi-regular.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsRegularImmersion

/-- A regular immersion of schemes is Koszul-regular. -/
@[instance]
theorem isKoszulRegular
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    IsKoszulRegularImmersion i := sorry

end IsRegularImmersion

namespace IsKoszulRegularImmersion

/-- A Koszul-regular immersion of schemes is `H₁`-regular. -/
@[instance]
theorem isH1Regular
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    IsH1RegularImmersion i := sorry

end IsKoszulRegularImmersion

namespace IsH1RegularImmersion

/-- An `H₁`-regular immersion of schemes is quasi-regular. -/
@[instance]
theorem isQuasiRegular
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsH1RegularImmersion i] :
    IsQuasiRegularImmersion i := sorry

end IsH1RegularImmersion

end AlgebraicGeometry
