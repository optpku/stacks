/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Refinement.Presheaf
import StacksCheckRecall

/-!
# Refinement through a locally surjective presheaf map

The reusable statement is owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Refinement.Presheaf`.
-/

open CategoryTheory

/- Lemma 25.7.4 [stacks 01GK]: a presheaf map which becomes surjective after sheafification is
canonically expressed as a locally surjective presheaf map; a hypercovering can be refined so
that its map in the prescribed degree factors through it. -/
@[stacks 01GK] #check
  @Hypercovering.Refinement.Presheaf.existsDegreeFactorization
