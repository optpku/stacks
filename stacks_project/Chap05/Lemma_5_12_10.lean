/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConnectedComponents.Clopen
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.10: in a quasi-compact space with a basis of quasi-compact opens and
quasi-compact intersections of quasi-compact opens, the connected component of `x` is the
intersection of its clopen neighborhoods. The reusable hypotheses are `PrespectralSpace` and
`QuasiSeparatedSpace`. -/
@[stacks 005F]
#check @PrespectralSpace.connectedComponent_eq_iInter_isClopen
