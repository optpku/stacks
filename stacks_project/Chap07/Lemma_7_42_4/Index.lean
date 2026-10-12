/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TypeSheafification.ULift
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 7.42.4 (04B8): the universe-indexed comparison infrastructure is owned by the
Type-valued sheafification API in ReasLib. -/
@[stacks 04B8 "universe comparison"] #check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallyInjective_type_of_univLE
