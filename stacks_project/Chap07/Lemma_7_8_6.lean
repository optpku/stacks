/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.8.6

The fixed-target-family refinement criterion is owned by ReasLib; this file
records the source-facing bundled and indexed formulations.
-/

@[expose] public section

namespace CategoryTheory

/- Lemma 7.8.6 (0G1L): a sheaf condition descends along a refinement of
fixed-target families when the corresponding pullback restriction maps are
injective. -/
@[stacks 0G1L] #check @SemiRepresentableFamily.Over.isSheafFor_of_refines_of_injective

@[stacks 0G1L] #check @SemiRepresentableFamily.Over.isSheafFor_ofArrows_refines_of_injective

end CategoryTheory
