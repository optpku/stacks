/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitCategory
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.18.2: explicit colimit category

The reusable quotient-category construction belongs to
`ReasLib.CategoryTheory.Sites.Cofiltered.ColimitCategory`.  This source file
only records the labelled Chapter 7 recall surface.
-/

@[expose] public section

/- Lemma 7.18.2 (09YL): for a cofiltered inverse system of sites, construct
the category whose objects and arrows are the common-lowering colimits of the
stage objects and arrows. -/
@[stacks 09YL "colimit category"] #check @CategoryTheory.CofilteredSiteDiagram.ColimitCategory

@[stacks 09YL "object representatives"] #check @CategoryTheory.CofilteredSiteDiagram.ObjRep

@[stacks 09YL "morphism representatives"] #check @CategoryTheory.CofilteredSiteDiagram.HomRep

@[stacks 09YL "cocone"] #check @CategoryTheory.CofilteredSiteDiagram.stageCoconeFunctor

@[stacks 09YL "descent"] #check @CategoryTheory.CofilteredSiteDiagram.exists_hom_rep
