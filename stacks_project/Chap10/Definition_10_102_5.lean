/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Rank
import StacksCheckRecall

/-!
# Definition 10.102.5

@stack 00MV
-/

@[expose] public section

/- Definition 10.102.5, tag `00MV`: exterior rank and its rank-minor ideal are owned by
`LinearMap.exteriorRank` and `LinearMap.rankMinorIdeal`; the latter carries the reusable
notation `I(φ)`. -/
@[stacks 00MV "exterior rank"]
#check @LinearMap.exteriorRank
@[stacks 00MV "exterior-rank bound"]
#check @LinearMap.exteriorRank_le_min
@[stacks 00MV "rank-minor ideal"]
#check @LinearMap.rankMinorIdeal
@[stacks 00MV "rank-minor generators"]
#check @LinearMap.det_submatrix_mem_rankMinorIdeal
