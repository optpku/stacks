module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.AffineFiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Proposition 59.95.6: if `K` is a field and `X` is an affine scheme of finite
type over `K`, then
`cohomologicalDimension X.left ≤ (topologicalKrullDim X.left).unbotD 0 +
  cohomologicalDimension (Spec (CommRingCat.of K))`. -/
@[stacks 0F0V] #check (AlgebraicGeometry.Scheme.cohomologicalDimension_le_dim_add :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K)
    [IsAffine X.left] [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})],
    Scheme.cohomologicalDimension X.left ≤
      ((topologicalKrullDim X.left).unbotD 0 : WithTop ℕ) +
        Scheme.cohomologicalDimension (Spec (CommRingCat.of K)))

#check (AlgebraicGeometry.Scheme.cohomologicalDimensionBound_dim_add :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K)
    [IsAffine X.left] [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})],
    Scheme.cohomologicalDimensionBound X.left
      (((topologicalKrullDim X.left).unbotD 0 : WithTop ℕ) +
        Scheme.cohomologicalDimension (Spec (CommRingCat.of K))))

end
