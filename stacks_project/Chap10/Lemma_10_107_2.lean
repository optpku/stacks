/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.107.2

@stack 04VP
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.107.2: the composition of two epimorphisms of rings is an epimorphism. This is the
general categorical composition law for epimorphisms, specialized in later use to
`CommRingCat` or `RingCat`. -/
@[stacks 04VP]
#check @CategoryTheory.epi_comp
