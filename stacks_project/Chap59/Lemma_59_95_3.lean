/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.AffineCurve
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.95.3: if `K` is a field and `X` is a 1-dimensional affine scheme of
finite type over `K`, then
`cohomologicalDimension X.left ≤ 1 + cohomologicalDimension (Spec (CommRingCat.of K))`. -/
@[stacks 0F0S] #check (AlgebraicGeometry.Scheme.cohomologicalDimension_le_one_add :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K)
    [IsAffine X.left] [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})],
    topologicalKrullDim X.left = 1 →
      Scheme.cohomologicalDimension X.left ≤
        1 + Scheme.cohomologicalDimension (Spec (CommRingCat.of K)))

#check (AlgebraicGeometry.Scheme.cohomologicalDimensionBound_one_add :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K)
    [IsAffine X.left] [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})],
    topologicalKrullDim X.left = 1 →
      Scheme.cohomologicalDimensionBound X.left
        (1 + Scheme.cohomologicalDimension (Spec (CommRingCat.of K))))

end
