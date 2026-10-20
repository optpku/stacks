module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.AffineSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.95.7: if `K` is a field and `X` is an affine scheme of finite type
over `K`, `E_a` is the set of points `x` of `X.left` with
`SchemeOverField.baseFieldTrdegAt X x ≤ a`, and `F` is an abelian torsion sheaf
on `X.left` étale with `abelianSheafSupport F ⊆ E_a`, then
`IsZero ((Sheaf.functorH X.left.smallEtaleTopology b).obj F)` whenever
`(a : WithTop ℕ) + Scheme.cohomologicalDimension (Spec (CommRingCat.of K)) < b`. -/
@[stacks 0F0W] #check (AlgebraicGeometry.Scheme.etaleCohomology_isZero_of_support_trdeg_le :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K)
    [IsAffine X.left] [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    {a b : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆ {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (hb : (a : WithTop ℕ) + Scheme.cohomologicalDimension (Spec (CommRingCat.of K)) < b),
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology b).obj F))

end
