/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Jacobson.Constructible
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.8 (1): the closed-point trace is a bijection on constructible
subsets in a Jacobson space. -/
@[stacks 005Y "constructible closed-point trace correspondence"]
#check JacobsonSpace.ClosedPoints.constructible_bijOn

/- The same correspondence is available as an equivalence of the canonical
constructible-subset subtypes, whose inverse is specified by its trace. -/
@[stacks 005Y "subtype equivalence for constructible traces"]
#check @JacobsonSpace.ClosedPoints.constructibleTraceEquiv

/- Lemma 5.18.8 (2): the constructible closed-point trace preserves and
reflects open retrocompact subsets. -/
@[stacks 005Y "preservation of open retrocompact subsets"]
#check @Topology.IsConstructible.isOpen_and_isRetrocompact_iff_closedPointsTrace

/- Lemma 5.18.8 (3): the constructible closed-point trace preserves and
reflects complements of open retrocompact subsets. -/
@[stacks 005Y "preservation of complements of open retrocompact subsets"]
#check @Topology.IsConstructible.isOpen_compl_and_isRetrocompact_compl_iff_closedPointsTrace
