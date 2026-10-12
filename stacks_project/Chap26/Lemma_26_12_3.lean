/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

@[expose] public section

/- Lemma 26.12.3: an affine scheme is reduced exactly when its coordinate ring is reduced. -/
@[stacks 01J2] #check AlgebraicGeometry.affine_isReduced_iff
