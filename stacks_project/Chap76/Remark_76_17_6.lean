module

public import stacks_project.Chap76.Remark_76_17_6_IdentityTarget
public import stacks_project.Chap76.Lemma_76_17_5_Action
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Remark 76.17.6 (1): when the target thickening is `𝟙 Y`, every prescribed
conormal map `A : a^* C_{Y/Y} ⟶ C_{X/X'}` is zero. -/
@[stacks 061D] #check
  (conormalMap_id_eq_zero :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
      (iX : X ⟶ X') (a : X ⟶ Y) [IsFirstOrderThickening iX]
      (A : (Modules.pullback a).obj (Hom.conormalSheaf (𝟙 Y)) ⟶ Hom.conormalSheaf iX),
      A = 0)

/- Remark 76.17.6 (2): for the identity target thickening, the sheaf of
Lemma 76.17.4 is the rule sending `U'` to the set of morphisms `U' ⟶ Y` over `B`
that restrict to `a` on `U`. -/
@[stacks 061D] #check
  (sections_id :
    ∀ {S : Scheme.{u}} {B X X' Y : AlgebraicSpace S}
      (sX' : X' ⟶ B) (sY : Y ⟶ B) (iX : X ⟶ X') (a : X ⟶ Y)
      [IsFirstOrderThickening iX] (U' : spacesEtaleSite X'),
      sections sX' sY iX (𝟙 Y) a 0 U' =
        {a' | a' ≫ sY = U'.hom ≫ sX' ∧
          closedι iX U' ≫ a' = toSource iX U' ≫ a})

section

variable {S : Scheme.{u}} {B X X' Y : AlgebraicSpace S}
variable (sX' : X' ⟶ B) (sY : Y ⟶ B)
variable (iX : X ⟶ X') (a : X ⟶ Y)
variable [IsFirstOrderThickening iX]

/- Remark 76.17.6 (3): identifying sheaves on `X` and `X'` via 76.9.1.1, the
sheaf `parameterSheaf sY iX (𝟙 Y) a` of `Hom_𝒪_X(a^* Ω_{Y/B}, C_{X/X'})` acts
on this identity-target sheaf of compatible lifts. -/
@[stacks 061D] #check
  (existsUnique_sectionPerturbation sX' sY iX (𝟙 Y) a 0 :
    ∀ (U' : spacesEtaleSite X') (θ : parameterHom sY iX (𝟙 Y) a U')
      (s : (sectionsSheaf sX' sY iX (𝟙 Y) a 0).obj.obj (op U')),
      ExistsUnique fun t : (sectionsSheaf sX' sY iX (𝟙 Y) a 0).obj.obj (op U') ↦
        IsSectionPerturbation sX' sY iX (𝟙 Y) a 0 U' θ s t)

end
