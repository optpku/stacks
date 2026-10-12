/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Colimit.Representable.Counterexamples.FiniteInitialSegment
import StacksCheckRecall

@[expose] public section

/-!
# Finite Initial Segments and Representable Colimits

The reusable diagram, colimit calculation, and representable-colimit obstruction are owned by
ReasLib. This file records the three source-facing conclusions of the example.
-/

open CategoryTheory Opposite

namespace CategoryTheory.Limits.Types.FiniteInitialSegment

/- Example 19.2.1 (05NP): the sequential colimit of the nonempty finite initial segments is
canonically equivalent to `ℕ`. -/
@[stacks 05NP "colimit of finite initial segments"] #check
  (colimitEquivNat : colimit diagram ≃ ℕ)

/- Example 19.2.1 (05NP): the canonical map from `ℕ` to the colimit does not factor through any
single finite stage. -/
@[stacks 05NP "no finite-stage factorization"] #check
  (fromNat_not_factors : ¬ colimitPost.FactorsThroughStage diagram fromNat)

/- Example 19.2.1 (05NP): consequently the representable-colimit comparison for `ℕ` is not
surjective. -/
@[stacks 05NP "representable comparison not surjective"] #check
  (comparison_not_surjective :
    ¬ Function.Surjective (colimit.post diagram (coyoneda.obj (op ℕ))))

end CategoryTheory.Limits.Types.FiniteInitialSegment
