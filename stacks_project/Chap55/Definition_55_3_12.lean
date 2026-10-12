/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality

/- Definition 55.3.12: A numerical type is minimal when it has no `(-1)`-index. -/
@[stacks 0C7A] #check (NumericalType.IsMinimal : NumericalType → Prop)
