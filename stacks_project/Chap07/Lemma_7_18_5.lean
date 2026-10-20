/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.DirectImage
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.18.5

The direct-image compatible family and its counit comparison live in
`ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.DirectImage`.  This file
keeps only the labelled Chapter 7 recall surface.
-/

@[expose] public section

/- Lemma 7.18.5 (0EXJ): direct images of a sheaf on the colimit site form a
compatible stage family; the colimit of its pullbacks maps isomorphically back
to the original set-valued sheaf. -/
@[stacks 0EXJ "direct image"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.DirectImage.pushforward

@[stacks 0EXJ "compatible family"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.DirectImage.family

@[stacks 0EXJ "stage counit"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.DirectImage.counit

@[stacks 0EXJ "colimit comparison"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.DirectImage.comparison

@[stacks 0EXJ "comparison isomorphism"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.DirectImage.comparison_isIso
