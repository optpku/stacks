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

/-- Lemma 59.95.3: if `K` is a field and `X` is a 1-dimensional affine scheme of
finite type over `K`, then
`cohomologicalDimension X.left ≤ 1 + cohomologicalDimension (Spec (CommRingCat.of K))`. -/
@[stacks 0F0S]
theorem cohomologicalDimension_le_one_add
    (hdim : topologicalKrullDim X.left = 1) :
    cohomologicalDimension X.left ≤
      1 + cohomologicalDimension (Spec (CommRingCat.of K)) := sorry

/-- Vanishing bound form of the affine finite-type dimension-one comparison for
cohomological dimension over a field. -/
theorem cohomologicalDimensionBound_one_add
    (hdim : topologicalKrullDim X.left = 1) :
    cohomologicalDimensionBound X.left
      (1 + cohomologicalDimension (Spec (CommRingCat.of K))) := sorry

end AlgebraicGeometry.Scheme

end
