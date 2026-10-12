/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap55.Theorem_55_18_1

/-
Remark 55.18.2 (Improving the bound)

This literature remark suggests possible improvements to the bound in Theorem 55.18.1,
but postpones a precise statement and proof. The formal entry therefore records only the
existing semistable-reduction theorem and the formula for `semistableReductionBound`.
-/
@[stacks 0CEK] #check AlgebraicGeometry.Curve.semistableReduction_genusGeTwo
@[stacks 0CEK] #check semistableReductionBound_eq
