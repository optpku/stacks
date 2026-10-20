module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets

/-!
# Functoriality of universe-aligned stacks of points

The morphisms of universe-aligned stacks induced by morphisms of algebraic spaces
preserve identities and composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The identity morphism of algebraic spaces induces the identity on the universe-aligned
`𝒮_X`. -/
theorem stackInSetsULift.map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSetsULift.map (𝟙 X) = 𝟙 (stackInSetsULift X) := sorry

/-- Universe-aligned `𝒮`-maps preserve composition of morphisms of algebraic spaces. -/
theorem stackInSetsULift.map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stackInSetsULift.map (f ≫ g) =
      stackInSetsULift.map f ≫ stackInSetsULift.map g := sorry

end AlgebraicGeometry.AlgebraicSpace
