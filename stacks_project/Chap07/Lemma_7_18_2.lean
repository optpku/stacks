/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitTopology
public import ReasLib.CategoryTheory.Sites.Cofiltered.Colimit.SheafPullback
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.18.2

The explicit colimit category and its selected colimit topology are reusable
site infrastructure.  Their owners are `Cofiltered.ColimitCategory` and
`Cofiltered.ColimitTopology` in ReasLib; this file is the labelled source
recall layer.
-/

@[expose] public section

/- Lemma 7.18.2 (09YL): the selected covers on the cofiltered colimit category
are the transported images of selected stage covers; they generate the least
topology for which every stage cocone functor is cover-preserving. -/
@[stacks 09YL "colimit site"] #check @CategoryTheory.CofilteredSiteDiagram.colimitSite

@[stacks 09YL "colimit topology"] #check @CategoryTheory.CofilteredSiteDiagram.colimitTopology

@[stacks 09YL "cocone continuity"] #check @CategoryTheory.CofilteredSiteDiagram.stageCoconeContinuous

@[stacks 09YL "least topology"] #check @CategoryTheory.CofilteredSiteDiagram.colimitTopology_isLeast

@[stacks 09YL "sheaf pullback"] #check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.compIso
