module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sections

/-!
# Infinitesimal deformations with identity target thickening

When the target thickening is the identity, the prescribed conormal map vanishes
and the compatible local deformations are the morphisms over `B` that restrict
to the original map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {B X X' Y : AlgebraicSpace S}

/-- A conormal map out of `a^* C_{Y/Y}` vanishes when the target thickening is
the identity morphism of `Y`. -/
theorem conormalMap_id_eq_zero (iX : X ⟶ X') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (A : (Modules.pullback a).obj (conormalSheaf (𝟙 Y)) ⟶ conormalSheaf iX) :
    A = 0 := sorry

/-- For an identity target thickening, a local lift is compatible if and only if
it is a morphism over `B` whose restriction along the source thickening is the
original map. -/
theorem isCompatible_id (sX' : X' ⟶ B) (sY : Y ⟶ B) (iX : X ⟶ X') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y) :
    IsCompatible sX' sY iX (𝟙 Y) a 0 U' a' ↔
      a' ≫ sY = U'.hom ≫ sX' ∧ closedι iX U' ≫ a' = toSource iX U' ≫ a :=
  sorry

/-- For an identity target thickening, compatible local deformations are exactly
the morphisms `U' ⟶ Y` over `B` that restrict to `a` on `U = X ×_{X'} U'`. -/
theorem sections_id (sX' : X' ⟶ B) (sY : Y ⟶ B) (iX : X ⟶ X') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    sections sX' sY iX (𝟙 Y) a 0 U' =
      {a' | a' ≫ sY = U'.hom ≫ sX' ∧
        closedι iX U' ≫ a' = toSource iX U' ≫ a} := sorry

/-- Membership in the identity-target sections is the over-`B` condition together
with restriction to `U` agreeing with `a`. -/
theorem mem_sections_id (sX' : X' ⟶ B) (sY : Y ⟶ B) (iX : X ⟶ X') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y) :
    a' ∈ sections sX' sY iX (𝟙 Y) a 0 U' ↔
      a' ≫ sY = U'.hom ≫ sX' ∧ closedι iX U' ≫ a' = toSource iX U' ≫ a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
