/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_95_1
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.KrullDimension
import Mathlib.Tactic.CrossRefAttribute

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

/-- Proposition 59.95.6: if `K` is a field and `X` is an affine scheme of finite
type over `K`, then
`cohomologicalDimension X.left ≤ (topologicalKrullDim X.left).unbotD 0 +
  cohomologicalDimension (Spec (CommRingCat.of K))`. -/
@[stacks 0F0V]
theorem cohomologicalDimension_le_dim_add :
    cohomologicalDimension X.left ≤
      @id (WithTop ℕ) ((topologicalKrullDim X.left).unbotD 0) +
        cohomologicalDimension (Spec (CommRingCat.of K)) := sorry

/-- Vanishing bound form of the affine finite-type comparison for cohomological
dimension over a field. -/
theorem cohomologicalDimensionBound_dim_add :
    cohomologicalDimensionBound X.left
      (@id (WithTop ℕ) ((topologicalKrullDim X.left).unbotD 0) +
        cohomologicalDimension (Spec (CommRingCat.of K))) := sorry

end AlgebraicGeometry.Scheme

end
