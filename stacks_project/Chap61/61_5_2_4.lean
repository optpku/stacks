/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.«61_5_2_4_Stage»
public import stacks_project.Chap61.«61_5_2_4_Transition»
import StacksCheckRecall

@[expose] public section

/- 61.5.2.4: for finite `E₁ ⊆ E₂ ⊆ A`, the canonical `A`-algebra map
`A_{E₁} → A_{E₂}` induces an affine scheme morphism `X_{E₂} ⟶ X_{E₁}`. -/
@[stacks 0972] #check Algebra.WLocalHull.spectrumMap
