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
Lemma 10.82.9 (Tag 05CI): composition preserves universal injectivity.

@stack 05CI
-/
@[stacks 05CI]
#check LinearMap.universallyInjective_comp
