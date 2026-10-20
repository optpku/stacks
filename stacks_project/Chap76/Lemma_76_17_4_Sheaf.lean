module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sheaf
public import stacks_project.Chap76.«76_17_4_1_Deformation»

/-!
# The sheaf of compatible local deformations of maps

Typed compatibility check for the sheaf of compatible local deformations on the
spaces-étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.sectionsSheaf sX' sY' iX iY a A :
  Sheaf (spacesEtaleTopology X') (Type (u + 1)))
