module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sheaf
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

/- Lemma 76.17.4: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `X ⊂ X'` and `Y ⊂ Y'` be first-order thickenings over `B`. Assume given a
morphism `a : X ⟶ Y` and a map `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` of `𝒪_X`-modules.
The rule sending `U'` in `(X')_spaces,étale` to the set of morphisms
`a' : U' ⟶ Y'` over `B` that restrict to `a` on `U = X ×_{X'} U'` and induce
the restriction of `A` defines a sheaf of sets on `(X')_spaces,étale`. -/
@[stacks 061A] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.sectionsPresheaf_isSheaf sX' sY' iX iY a A :
    Presheaf.IsSheaf (spacesEtaleTopology X')
      (sectionsPresheaf sX' sY' iX iY a A))
