module

public import stacks_project.Chap59.Definition_59_95_1
public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : SchemeOverField K)
variable [IsAffine X.left] [Algebraic X]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.95.7: if `K` is a field and `X` is an affine scheme of finite type
over `K`, `E_a` is the set of points `x` of `X.left` with
`SchemeOverField.baseFieldTrdegAt X x ≤ a`, and `F` is an abelian torsion sheaf
on `X.left` étale with `abelianSheafSupport F ⊆ E_a`, then
`IsZero ((Sheaf.functorH X.left.smallEtaleTopology b).obj F)` whenever
`(a : WithTop ℕ) + cohomologicalDimension (Spec (CommRingCat.of K)) < b`. -/
@[stacks 0F0W]
theorem etaleCohomology_isZero_of_support_trdeg_le
    {a b : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆ {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (hb : (a : WithTop ℕ) + cohomologicalDimension (Spec (CommRingCat.of K)) < b) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology b).obj F) := sorry

end AlgebraicGeometry.Scheme

end
