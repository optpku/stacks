module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Implications among regular immersions of algebraic spaces

Koszul-regular immersions are `H₁`-regular, `H₁`-regular immersions are
quasi-regular, and quasi-regular immersions are immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Koszul-regular immersion of algebraic spaces is `H₁`-regular. -/
@[instance]
theorem IsKoszulRegularImmersion.isH1Regular {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    IsH1RegularImmersion i := sorry

/-- An `H₁`-regular immersion of algebraic spaces is quasi-regular. -/
@[instance]
theorem IsH1RegularImmersion.isQuasiRegular {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsH1RegularImmersion i] :
    IsQuasiRegularImmersion i := sorry

/-- A quasi-regular immersion of algebraic spaces is an immersion. -/
@[instance]
theorem IsQuasiRegularImmersion.isImmersion {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsQuasiRegularImmersion i] :
    IsImmersion i := sorry

end AlgebraicGeometry.AlgebraicSpace
