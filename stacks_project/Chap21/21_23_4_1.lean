/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# 21.23.4.1

The displayed Milnor sequence is the direct source-facing reading of the reusable objectwise
cohomology row; this item introduces no additional object or wrapper.
-/

/- 21.23.4.1: for a ringed site `X`, an object `U : X`, a sequential inverse system `(K_n)` in
`D(𝒪_X)`, and a chosen derived limit `K`, the groups `H^m(U, K)` fit into
`0 ⟶ R¹ lim_n H^(m - 1)(U, K_n) ⟶ H^m(U, K) ⟶ lim_n H^m(U, K_n) ⟶ 0`. -/
@[stacks 0BKX]
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyShortExact

#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyTower
#check @CategoryTheory.SequentialInverseSystem.firstDerivedLimit
