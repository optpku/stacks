/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.EnoughObjects.Presentation
import StacksCheckRecall

@[expose] public section

/- Lemma 7.12.5: covers by objects with a property give coequalizer presentations by sheafified
representables. The reusable owners are in ReasLib. -/
#check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty
@[stacks 00WS] #check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty.existsCoequalizerPresentation
