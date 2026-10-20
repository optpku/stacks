module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Action
public import stacks_project.Chap76.Lemma_76_17_2_Comparison

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

/- The unique local perturbation of a compatible lift. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.existsUnique_sectionPerturbation sX' sY' iX iY a A :
    ∀ (U' : spacesEtaleSite X') (θ : parameterHom sY' iX iY a U')
      (s : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')),
      ExistsUnique fun t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U') ↦
        IsSectionPerturbation sX' sY' iX iY a A U' θ s t)

