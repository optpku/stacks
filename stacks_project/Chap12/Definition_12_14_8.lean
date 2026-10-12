/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
variable (K : CochainComplex C ℤ) (i k : ℤ)

/- Definition 12.14.8: the canonical shift comparison identifies `H^(i + k)(K)` with
`H^i(K⟦k⟧)`. -/
@[stacks 011H]
#check (((CochainComplex.ShiftSequence.shiftIso C k i (i + k) (add_comm k i)).app K).symm :
  K.homology (i + k) ≅ (K⟦k⟧).homology i)

/- The comparison is owned by the cochain-homology shift sequence. -/
#check CochainComplex.ShiftSequence.shiftIso
