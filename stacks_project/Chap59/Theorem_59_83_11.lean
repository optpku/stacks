module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap59.Proposition_59_54_2_Leray_spectral_sequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- Theorem 59.83.11 (1): étale cohomology of a locally torsion abelian sheaf `F` on `Xₑₜ`
vanishes in degrees `q ≥ 3`. Separatedness of `X` over `k` is not assumed. -/
@[stacks 03RT]
public theorem etaleCohomology_isZero_of_ge_three
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    {q : ℕ} (hq : 2 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Theorem 59.83.11 (2): if `X` is affine, then étale cohomology of a locally torsion abelian
sheaf `F` on `Xₑₜ` also vanishes in degree `2`. Separatedness of `X` over `k` is not assumed. -/
@[stacks 03RT]
public theorem etaleCohomology_h2_isZero_of_isAffine
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    (h_affine : IsAffine X.left) :
    IsZero (etaleCohomology X.left F 2) := sorry

/-- If `X` is affine, étale cohomology of a locally torsion abelian sheaf `F` on `Xₑₜ`
vanishes in all degrees `q > 1`. This packages vanishing in degree `2` with vanishing for
`q ≥ 3`. -/
public theorem etaleCohomology_isZero_of_isAffine_gt_one
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
