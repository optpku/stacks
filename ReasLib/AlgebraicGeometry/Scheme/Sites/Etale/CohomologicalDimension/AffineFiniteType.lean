/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : SchemeOverField K)
variable [IsAffine X.left] [Algebraic X]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]

/-- An affine scheme of finite type over a field has vanishing locally torsion
étale sheaf cohomology above its Krull dimension plus the cohomological dimension
of the field, with the dimension of the empty scheme taken to be zero. -/
theorem cohomologicalDimensionBound_dim_add :
    cohomologicalDimensionBound X.left
      (((topologicalKrullDim X.left).unbotD 0 : WithTop ℕ) +
        cohomologicalDimension (Spec (CommRingCat.of K))) := sorry

/-- The cohomological dimension of an affine scheme of finite type over a field
is at most its Krull dimension plus the cohomological dimension of the field,
with the dimension of the empty scheme taken to be zero. -/
theorem cohomologicalDimension_le_dim_add :
    cohomologicalDimension X.left ≤
      ((topologicalKrullDim X.left).unbotD 0 : WithTop ℕ) +
        cohomologicalDimension (Spec (CommRingCat.of K)) := by
  exact cohomologicalDimension_le_of_bound X.left
    (((topologicalKrullDim X.left).unbotD 0 : WithTop ℕ) +
      cohomologicalDimension (Spec (CommRingCat.of K)))
    (cohomologicalDimensionBound_dim_add X)

end AlgebraicGeometry.Scheme

end
