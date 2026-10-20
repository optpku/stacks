/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.Basic
public import StacksCheckRecall.CommandCrossRef

/-!
# Situation 7.18.1

The reusable owner for a cofiltered inverse diagram of finite sites is
`CategoryTheory.CofilteredSiteDiagram`. This source file is intentionally a
recall layer: selected precoverages are primitive data, while generated stage
topologies and the site-morphism interface are derived in ReasLib.
-/

@[expose] public section

/- Situation 7.18.1 (0A34): a cofiltered inverse system of sites with finite
selected covers, the literal Stacks site axioms, and continuous
representably-flat transition functors. -/
@[stacks 0A34 "diagram"] #check @CategoryTheory.CofilteredSiteDiagram

@[stacks 0A34 "stage"] #check @CategoryTheory.CofilteredSiteDiagram.stage

@[stacks 0A34 "transition"] #check @CategoryTheory.CofilteredSiteDiagram.stageFunctor

@[stacks 0A34 "topology"] #check @CategoryTheory.CofilteredSiteDiagram.stageTopology

@[stacks 0A34 "finite refinement"] #check @CategoryTheory.GrothendieckTopology.finiteRefinement_of_finite

@[stacks 0A34 "coverage"] #check @CategoryTheory.Precoverage.HasFactoringPullbacks.toCoverage

@[stacks 0A34 "continuity"] #check @CategoryTheory.Functor.Precoverage.IsContinuous.toContinuous

@[stacks 0A34 "sheaf pullback"] #check @CategoryTheory.CofilteredSiteDiagram.stageSheafPullbackCompIso
