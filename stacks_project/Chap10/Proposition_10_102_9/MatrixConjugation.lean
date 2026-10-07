module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Operations
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.RankEquiv
import StacksCheckRecall

/-!
# Coordinate invariance of minor ideals

Proposition 10.102.9 uses coordinate changes that preserve fixed-size minor ideals and the
associated exterior-rank invariants. This support file recalls the shared APIs.

@stack 00N1
-/

@[expose] public section

@[stacks 00N1 "minor ideal under transpose"]
#check @Matrix.minorIdeal_transpose_eq

@[stacks 00N1 "minor ideal under right multiplication"]
#check @Matrix.minorIdeal_mul_right_le

@[stacks 00N1 "exterior rank under coordinate equivalence"]
#check @LinearMap.exteriorRank_comp_equiv_eq

@[stacks 00N1 "rank-minor ideal under coordinate equivalence"]
#check @LinearMap.rankMinorIdeal_comp_equiv_eq

@[stacks 00N1 "exterior rank under finite free coordinate equivalence"]
#check @LinearMap.exteriorRank_eq_of_equiv

@[stacks 00N1 "rank-minor ideal under finite free coordinate equivalence"]
#check @LinearMap.rankMinorIdeal_eq_of_equiv
