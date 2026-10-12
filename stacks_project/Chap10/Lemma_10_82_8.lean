/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.82.8 (Tag 05CH): right tensoring preserves universal injectivity.

@stack 05CH
-/
@[stacks 05CH]
#check LinearMap.universallyInjective_rTensor
