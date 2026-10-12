/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_17_5_Action
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX)

/- Lemma 76.17.5 (1): Same notation and assumptions as in Lemma 76.17.4.
Identifying sheaves on X and X' via 76.9.1.1, the sheaf
Hom_𝒪_X (a^* Ω_{Y/B}, C_{X/X'}) acts on the sheaf of compatible lifts. -/
@[stacks 061C] #check
  (existsUnique_sectionPerturbation sX' sY' iX iY a A :
    ∀ (U' : spacesEtaleSite X') (θ : parameterHom sY' iX iY a U')
      (s : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')),
      ExistsUnique fun t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U') ↦
        IsSectionPerturbation sX' sY' iX iY a A U' θ s t)

/- Lemma 76.17.5 (2): The action is simply transitive for any object U' of
(X')_spaces,étale over which the sheaf of compatible lifts has a section. -/
@[stacks 061C] #check
  (act_simplyTransitive sX' sY' iX iY a A :
    ∀ (U' : spacesEtaleSite X')
      (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')),
      ExistsUnique fun θ : parameterHom sY' iX iY a U' ↦
        IsSectionPerturbation sX' sY' iX iY a A U' θ s t)
