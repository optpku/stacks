module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-!
# Residue-field transcendence degree under composition

The pointwise residue-field transcendence degree of locally finite type
algebraic-space morphisms is additive under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For composable locally finite type morphisms, the residue-field
transcendence degree at a point is the sum of the degrees for the first
morphism at that point and the second morphism at its image. -/
theorem residueFieldTrdegAt.comp_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : Points X) :
    residueFieldTrdegAt (f ≫ g) x =
      residueFieldTrdegAt f x + residueFieldTrdegAt g (Points.map f x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
