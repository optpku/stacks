/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConnectedComponents.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 5.22.5: the clopen-neighborhood characterization of components
makes `ConnectedComponents X` profinite for compact `X`. -/
@[stacks 0900 "profinite connected-components quotient"]
#check ConnectedComponents.exists_profinite_of_connectedComponent_eq_iInter_isClopen
