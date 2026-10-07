module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.LocalAtTarget

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IndQuasiAffineHom

/-- Ind-quasi-affine scheme morphisms are stable under composition. -/
instance stableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@IndQuasiAffineHom : MorphismProperty Scheme.{u}) := sorry

/-- The composite of two ind-quasi-affine scheme morphisms is ind-quasi-affine. -/
theorem comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IndQuasiAffineHom f) (hg : IndQuasiAffineHom g) :
    IndQuasiAffineHom (f ≫ g) := sorry

end AlgebraicGeometry.IndQuasiAffineHom
