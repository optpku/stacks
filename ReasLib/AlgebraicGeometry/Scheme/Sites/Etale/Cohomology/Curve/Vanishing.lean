module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Leray

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

/-- Étale cohomology of a locally torsion abelian sheaf on a finite-type scheme of
dimension at most one over an algebraically closed field vanishes in degrees at least three. -/
public theorem etaleCohomology_isZero_of_ge_three
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    {q : ℕ} (hq : 2 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

/-- Degree-two étale cohomology of a locally torsion abelian sheaf on an affine finite-type
scheme of dimension at most one over an algebraically closed field vanishes. -/
public theorem etaleCohomology_h2_isZero_of_isAffine
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    (h_affine : IsAffine X.left) :
    IsZero (etaleCohomology X.left F 2) := sorry

/-- Étale cohomology of a locally torsion abelian sheaf on an affine finite-type scheme
of dimension at most one over an algebraically closed field vanishes in degrees greater than one. -/
public theorem etaleCohomology_isZero_of_isAffine_gt_one
    (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
    (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (etaleCohomology X.left F q) := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
