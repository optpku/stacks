module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Functorial

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z W Z' W' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
variable (f : Z ⟶ W) (g : X ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
variable (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.comparison
    iZ fZ iW fW f g sq : Z' ⟶ W')
