/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.ChainShiftSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
variable (K : ChainComplex C ℤ) (k i : ℤ)

/- Definition 12.14.2: shifting a chain complex by `k` canonically identifies
`H_(i + k)(K)` with `H_i(K⟦k⟧)`. -/
@[stacks 011B]
#check (ChainComplex.Homology.ShiftSequence.iso K k i :
  K.homology (i + k) ≅ (K⟦k⟧).homology i)

/- The owner is the shift-sequence structure on the ordinary chain-homology functor. -/
#check ChainComplex.Homology.ShiftSequence.instChain
