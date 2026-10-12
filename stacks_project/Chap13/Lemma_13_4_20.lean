/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Homological.Exact
import StacksCheckRecall

@[expose] public section

-- Lemma 13.4.20: Mathlib owns precomposition of a homological functor by a
-- triangulated functor; ReasLib supplies exact target-side postcomposition.
@[stacks 05QZ] #check @CategoryTheory.Functor.IsHomological

@[stacks 05QZ] #check @CategoryTheory.Functor.isHomological_comp_exact
