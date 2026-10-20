/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitPullback

/-!
# Lemma 7.18.3

The reusable owner for pullback sections on a cofiltered colimit site is
`CategoryTheory.CofilteredSiteDiagram.ColimitPullback`.  This chapter file
preserves the two source assertions as recalls while downstream developments
import the ReasLib owner directly.
-/

@[expose] public section

/- Lemma 7.18.3 (0A35) (1): every cocone functor from a stage site to the
colimit site is a morphism of sites. -/
@[stacks 0A35 "(1)"] #check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.stageCocone_isMorphismOfSites

/- Lemma 7.18.3 (0A35) (2): the canonical filtered-colimit comparison on
stage-pullback sections is invertible. -/
@[stacks 0A35 "(2)"] #check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison_isIso

#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.stagePullback
#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.sectionDiagram
#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison
#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison_bijective
