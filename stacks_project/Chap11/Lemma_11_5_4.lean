/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Degree
import StacksCheckRecall

@[expose] public section

@[stacks 074N] #check @CSA.finrank_isSquare
#check @CSA.degree
#check @CSA.degree_sq_eq_finrank

end
