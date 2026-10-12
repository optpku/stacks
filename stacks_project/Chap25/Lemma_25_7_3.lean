/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Refinement
import StacksCheckRecall

namespace CategoryTheory

/- Lemma 25.7.3 [stacks 01GJ]: a covering map into degree `k` of a hypercovering can be factored
through the degree-`k` map of a refining hypercovering. The topology-relative, fixed-target API
is owned by `CategoryTheory.Hypercovering.Refinement.existsDegreeFactorization`. -/
@[stacks 01GJ] #check @Hypercovering.Refinement.existsDegreeFactorization

end CategoryTheory
