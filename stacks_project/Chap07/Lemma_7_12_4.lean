/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Cover
import StacksCheckRecall

@[expose] public section

/- Lemma 7.12.4: the canonical map from the coproduct of sheafified representables attached to a
covering family is locally surjective. The reusable owner is in ReasLib. -/
#check @CategoryTheory.GrothendieckTopology.sheafifiedRepresentableCoverMap
@[stacks 00WT] #check @CategoryTheory.GrothendieckTopology.sheafifiedRepresentableCoverMap_isLocallySurjective
