/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.GeometricallyNormal
import StacksCheckRecall

/-!
# Definition 10.165.2

@stack 0380
-/

@[expose] public section

/- Definition 10.165.2 (Tag 0380): geometric normality of a commutative algebra over a field is
the canonical predicate `Algebra.IsGeometricallyNormal` from
`ReasLib.RingTheory.Normal.GeometricallyNormal`.  Its base-change field and its explicit
universal formulation are available directly from that shared owner. -/
@[stacks 0380]
#check @Algebra.IsGeometricallyNormal
@[stacks 0380 "normality after field base change"]
#check @Algebra.IsGeometricallyNormal.isNormalRing_baseChange
@[stacks 0380 "tensor-product characterization"]
#check @Algebra.IsGeometricallyNormal.iff_forall_isNormalRing_tensorProduct
