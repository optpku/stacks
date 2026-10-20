module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sections
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

/- 76.17.4.1: to `U' : spacesEtaleSite X'`, assign the set of morphisms
`a' : U'.left ⟶ Y'` over `B` which restrict to `a` on `X ×_{X'} U'` and
induce the prescribed restriction of the conormal map `A`. -/
@[stacks 061B] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.sections sX' sY' iX iY a A :
    (U' : spacesEtaleSite X') → Set (U'.left ⟶ Y'))
