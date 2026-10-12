/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Equation 17.31.1.1 (08TK): a compatible change of base and algebra is a commutative square in
the category of sheaves of commutative rings. -/
@[stacks 08TK]
#check @CommSq

#check @CommSq.w
