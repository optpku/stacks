/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/- Definition 26.23.1: a monomorphism of schemes is a monomorphism in the
ambient category. -/
@[stacks 01L2] #check CategoryTheory.Mono
