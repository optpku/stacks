/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
import StacksCheckRecall

@[expose] public section

/- Definition 90.14.4: a versal formal object ξ of a predeformation category F
is minimal when every morphism of formal objects ξ' ⟶ ξ has
Function.Surjective underlying complete-local algebra map. A minimal versal
formal object is also called miniversal. This is owned by
FormalObject.IsMinimalVersal. -/
@[stacks 06T4] #check FormalObject.IsMinimalVersal

#check FormalObject.IsMinimalVersal.spec
