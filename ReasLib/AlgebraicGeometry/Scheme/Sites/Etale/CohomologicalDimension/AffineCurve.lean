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

/-- A one-dimensional affine scheme of finite type over a field has vanishing
locally torsion étale sheaf cohomology above one plus the cohomological dimension
of the field. -/
theorem cohomologicalDimensionBound_one_add
    (hdim : topologicalKrullDim X.left = 1) :
    cohomologicalDimensionBound X.left
      (1 + cohomologicalDimension (Spec (CommRingCat.of K))) := sorry

/-- The cohomological dimension of a one-dimensional affine scheme of finite
type over a field is at most one plus the cohomological dimension of the field. -/
theorem cohomologicalDimension_le_one_add
    (hdim : topologicalKrullDim X.left = 1) :
    cohomologicalDimension X.left ≤
      1 + cohomologicalDimension (Spec (CommRingCat.of K)) := by
  exact cohomologicalDimension_le_of_bound X.left
    (1 + cohomologicalDimension (Spec (CommRingCat.of K)))
    (cohomologicalDimensionBound_one_add X hdim)

end AlgebraicGeometry.Scheme

end
