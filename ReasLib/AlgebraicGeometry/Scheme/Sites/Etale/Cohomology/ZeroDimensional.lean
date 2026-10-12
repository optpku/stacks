/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Positive-degree étale cohomology vanishes for an affine scheme whose points
are closed and whose residue fields are separably algebraically closed. -/
theorem etaleCohomology_isZero_of_affine_closedPoints_sepClosedResidue
    (S : Scheme.{u}) [IsAffine S]
    (h_closed : ∀ x : S, IsClosed ({x} : Set S))
    (h_res : ∀ x : S, IsSepClosed (S.residueField x))
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (i : ℕ) (hi : 0 < i)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero ((Sheaf.functorH S.smallEtaleTopology i).obj F) := sorry

end AlgebraicGeometry.Scheme
