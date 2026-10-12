/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.12.10

@stack 00DF
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.12.10: tensoring a right exact sequence of `R`-modules with a fixed module `N`
preserves exactness. The canonical owner declarations are `rTensor_exact` for the exact pair and
`LinearMap.rTensor_surjective` for the terminal surjection. -/
@[stacks 00DF "exact pair after tensoring"]
#check @rTensor_exact
@[stacks 00DF "terminal surjection after tensoring"]
#check @LinearMap.rTensor_surjective
