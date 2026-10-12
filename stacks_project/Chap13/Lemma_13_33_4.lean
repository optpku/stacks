/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Subsequence
import StacksCheckRecall

@[expose] public section

/-!
Lemma 13.33.4 (`0CRJ`): a strictly increasing subsequence has the same
sequential homotopy-colimit objects as the original diagram. The generic
comparison is owned by `CategoryTheory.HomotopyColimit.IsOf`, so the chapter
entry is only a tagged canonical recall.
-/

open CategoryTheory

#check @CategoryTheory.SequentialDiagram.toSubsequence
#check @CategoryTheory.SequentialDiagram.toSubsequence_app
#check @CategoryTheory.HomotopyColimit.Presentation.Subsequence.Comparison.selectedStage_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.Subsequence.Comparison.selectedStage_naturality_inv
@[stacks 0CRJ] #check @CategoryTheory.HomotopyColimit.IsOf.nonemptyIsoOfSubsequence
@[stacks 0CRJ] #check @CategoryTheory.HomotopyColimit.IsOf.subsequence_iff
