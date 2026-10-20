module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.96.2 (1): if `K` is a field and `f : X ⟶ Y` is a morphism of finite type
schemes over `K`, then `Hom.cohomologicalDimension f.left ≠ ⊤`. -/
@[stacks 0F10] #check (AlgebraicGeometry.Scheme.Hom.cohomologicalDimension_ne_top :
    ∀ {K : Type u} [Field K] {X Y : SchemeOverField K} [Algebraic X] [Algebraic Y]
    (f : X ⟶ Y)
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})],
    Hom.cohomologicalDimension f.left ≠ ⊤)

/- Lemma 59.96.2 (2): if `K` is a field with
`cohomologicalDimension (Spec (CommRingCat.of K)) ≠ ⊤`, then every finite type
scheme `X` over `K` has `cohomologicalDimension X.left ≠ ⊤`. -/
@[stacks 0F10] #check (AlgebraicGeometry.Scheme.cohomologicalDimension_ne_top :
    ∀ {K : Type u} [Field K] {X : SchemeOverField K} [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (hK : cohomologicalDimension (Spec (CommRingCat.of K)) ≠ ⊤),
    cohomologicalDimension X.left ≠ ⊤)

end AlgebraicGeometry.Scheme

end
