/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.DerivedCategory.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

/- Lemma 20.37.8 (08U2): a single degree-dependent bound for
`H^p(U, H^(m-p)(E))` on every member of a topological basis makes every compatible map from `E`
to a derived limit of its lower truncation tower an isomorphism. -/
@[stacks 08U2 "uniform basiswise eventual vanishing makes the truncation comparison invertible"]
#check @Comparison.isIso_of_basisEventual

@[stacks 08U2 "uniform basiswise eventual vanishing condition"]
#check @Basis.Eventual
@[stacks 08U2 "uniform basiswise eventual vanishing implies local vanishing"]
#check @Basis.Eventual.toLocal

end
