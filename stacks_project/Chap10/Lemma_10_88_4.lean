/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Domination.Pushout

/-!
# Pushout criterion for tensor-kernel domination

@stack 0AUM
-/

@[expose] public section

/- Lemma 10.88.4 is owned by the reusable pushout API for tensor-kernel domination. -/

@[stacks 0AUM]
#check @LinearMap.Dominates.iff_universallyInjective_pushoutInr
