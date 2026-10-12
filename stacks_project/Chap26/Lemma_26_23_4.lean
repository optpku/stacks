/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/- Lemma 26.23.4: a composite of monomorphisms is a monomorphism. -/
@[stacks 01L5] #check CategoryTheory.mono_comp
