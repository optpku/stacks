/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section

/- `T2Space.isSeparatedMap` is the canonical, continuity-free bridge from a Hausdorff source to
the separated-map predicate. -/

/- Canonical core: every map from a Hausdorff source is separated. -/
@[stacks 0CY3 "Hausdorff source implies separated map"]
#check T2Space.isSeparatedMap
