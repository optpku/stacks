/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.4.1

The three consecutive-zero identities are canonical consequences of
distinguishedness in Mathlib's `Pretriangulated` API.
-/

@[stacks 0146] #check @CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂

@[stacks 0146] #check @CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₂₃

@[stacks 0146] #check @CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₃₁
