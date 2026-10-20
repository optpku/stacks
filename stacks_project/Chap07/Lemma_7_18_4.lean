/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Colimit
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.18.4

Compatible stage families, their colimit sheaves, and the section comparison
live in `ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Colimit`.  This
file keeps only the labelled Chapter 7 recall surface.
-/

@[expose] public section

/- Lemma 7.18.4 (09YN): a compatible inverse system of sheaves on a
cofiltered system of sites has a colimit sheaf on the explicit colimit site;
the over-category colimit of its sections maps isomorphically to the
corresponding colimit-sheaf section. -/
@[stacks 09YN "colimit pullback capability"] #check @CategoryTheory.CofilteredSiteDiagram.ColimitSheafPullback

@[stacks 09YN "colimit sheaf"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.colimitSheaf

@[stacks 09YN "section diagram"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Section.diagram

@[stacks 09YN "section comparison"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Section.comparison

@[stacks 09YN "comparison isomorphism"] #check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Section.comparison_isIso
