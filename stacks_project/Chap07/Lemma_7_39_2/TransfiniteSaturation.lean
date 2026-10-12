/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix

/-!
# Strict-below scheduled saturation

The ReasLib open-prefix section and cut-extension APIs own strict-predecessor
diagrams, their telescope anchors, and the resulting compatible extension.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "transfinite saturation transport"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.restrictionFunctor
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.restrictionFunctor.sections_restrict

@[stacks 00YP "strict-below refinement diagram"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.Section.topDiagram
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.Section.telescopeExtension

@[stacks 00YP "strict-below refinement anchor"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.Section.telescopePrefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension
