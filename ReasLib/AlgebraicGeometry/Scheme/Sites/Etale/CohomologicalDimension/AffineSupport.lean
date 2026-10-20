module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import Mathlib.AlgebraicGeometry.AffineScheme

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

/-- A locally torsion abelian étale sheaf on an affine scheme of finite type over a field,
supported at points of residue-field transcendence degree at most `a`, has vanishing
cohomology in degrees strictly above `a` plus the cohomological dimension of the field. -/
theorem etaleCohomology_isZero_of_support_trdeg_le
    {a b : ℕ} (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F)
    (hsupp : abelianSheafSupport F ⊆ {x | SchemeOverField.baseFieldTrdegAt X x ≤ a})
    (hb : (a : WithTop ℕ) + cohomologicalDimension (Spec (CommRingCat.of K)) < b) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology b).obj F) := sorry

end AlgebraicGeometry.Scheme

end
