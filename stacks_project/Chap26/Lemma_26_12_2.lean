/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Reduced
import StacksCheckRecall

@[expose] public section

/- Lemma 26.12.2: a scheme is reduced exactly when every open section ring is reduced. -/
@[stacks 01J1] #check AlgebraicGeometry.Scheme.isReduced_iff
