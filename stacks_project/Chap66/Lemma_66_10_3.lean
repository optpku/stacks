module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.10.3 (1): let `S` be a scheme and let `X` be an algebraic space over `S`. The
dimension of `X` equals the supremum of the dimensions of the local rings of `X`. -/
@[stacks 0BAN]
theorem dimension_eq_iSup_localRingDimAt {S : Scheme.{u}} (X : AlgebraicSpace S) :
    dimension X = ⨆ x : Points X, localRingDimAt x :=
  sorry

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Lemma 66.10.3 (2): let `S` be a scheme and let `X` be an algebraic space over `S`. The
dimension of `X` equals the supremum of `dimensionAt x` for `x : Points X`. -/
@[stacks 0BAN] #check
  (dimension_eq_iSup_dimensionAt X :
    dimension X = ⨆ x : Points X, dimensionAt x)

end AlgebraicGeometry.AlgebraicSpace
